#!/bin/bash

TIMEFORMAT="%U %S" # Important: %User time + %System time
DIRECTORIES="mist wahl-kroening medical bug_tracking soter"
TIMEOUT=2000

function echo_time {
    echo "[$(date +"%H:%M:%S")] $1 $2 $3 $4 $5 $6"
}

# Arguments
if [ "$1" = "" ]; then
    program="tacas"
else
    program=$1
fi

# Perform benchmarks
for dir in $DIRECTORIES
do
    files=$(find ./$dir -type f -name "*.spec") # .spec of all subdirectories
    logfile=./$dir/results/$program.log

    cp $logfile $logfile".bak" 2> /dev/null
    > $logfile # Clear logs file

    echo_time "### Processing" $dir "###"

    skip=1
    for file in $files
    do
	if [ "$skip" -lt "0" ]; then
	    echo_time " Skiping $file."
	    skip=$(($skip+1))
	    continue
	fi

	echo_time " Verifying $file..."

	# Obtain output and running time
	if [ "$program" = "tacas" ]; then
	    (time (timeout $TIMEOUT python ../main.py $file)) 1> temp_output \
	                                                      2> temp_time
	    output=$(cat temp_output)
	elif [ "$program" = "mist-backward" ]; then
	    (time (timeout $TIMEOUT mist --backward $file)) 1> temp_output \
	                                                    2> temp_time
	    output=$(python parse_output.py temp_output --tool $program)
	elif [ "$program" = "petrinizer" ]; then
	    (time (timeout $TIMEOUT ../petrinizer/src/main \
		              -refinement-int $file.pl)) 1> temp_output \
	                                                 2> temp_time
	    result=$?
	    if [ "$result" = "0" ]; then
		output="Safe"
	    elif [ "$result" = "1" ]; then
		output="Unsafe"
	    elif [ "$result" = "2" ]; then
		output="Unknown"
	    fi
	elif [ "$program" = "bfc" ]; then
	    (time (timeout $TIMEOUT ../bfc/bfc --target $file.tts.prop \
		                               $file.tts)) 1> temp_output \
	                                                   2> temp_time

	    tail -n 1 temp_time > temp_time.tail && mv temp_time.tail temp_time
	    output=$(python parse_output.py temp_output --tool $program)
	fi

	# Process timing
	if [ "$output" = "" ]; then
	    output="Timeout"
	    elapsed=$((1000*$TIMEOUT))
	else
	    elapsed=$(cat temp_time | awk '{print 1000*($1+$2);}')	    
	fi

	# Clear temporary files
	rm temp_output temp_time

	# Outputs
	echo_time "   Result:" $output          # Console ouput
	echo_time "   Time:  " $elapsed "ms"    #

	echo $file $output $elapsed >> $logfile # Logs output
    done

    # Print directory summary
    echo_time " Summary:"
    python summary.py $dir --tool $program
done

# Print overall summary if more than one directory
list=( $DIRECTORIES )

if [ "${#list[@]}" -gt "1" ]; then
    echo_time "### Overall summary ###"
    python summary.py $DIRECTORIES --mode overall --tool $program
fi
