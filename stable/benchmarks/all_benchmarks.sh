#!/bin/bash

TOOLS="tacas petrinizer mist-backward bfc"

for tool in $TOOLS
do
    ./benchmark.sh $tool
done

