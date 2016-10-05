#expected result: safe
vars
    x0 x1 x2 x3 x4

rules
    x0 >= 1,
    x1 >= 1,
    x2 >= 1 ->
		    x0' = x0-1,
		    x2' = x2-1,
		    x3' = x3+1;

    x0 >= 1,
    x1 >= 1,
    x2 >= 1 ->
		    x0' = x0-1,
		    x1' = x1-1,
		    x4' = x4+1;

    x3 >= 1 ->
		    x0' = x0+1,
		    x2' = x2+1,
		    x3' = x3-1;

    x4 >= 1 ->
		    x0' = x0+1,
		    x1' = x1+1,
		    x4' = x4-1;
init
    x0 >= 1, x1 = 1, x2 = 1, x3 = 0, x4 = 0

target
    x3 >= 1, x4 >= 1
    x3 >= 2
    x4 >= 2

invariants
	x0=1, x2=1, x3=2
	x0=1, x1=1, x4=2
