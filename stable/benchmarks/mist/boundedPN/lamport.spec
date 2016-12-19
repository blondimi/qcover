#expected result: safe
vars
     p1 p2 p3 x_eq_0 x_eq_1 y_eq_1 q1 q2 q3 q4 q5

rules
    p1 >= 1 , x_eq_0 >= 1 ->
		    p1' = p1-1
		, p2' = p2+1
		, x_eq_0' = x_eq_0-1
		, x_eq_1' = x_eq_1+1 ;

    p2 >= 1 , x_eq_1 >= 1 ->
		    p2' = p2-1
		, p3' = p3+1
		, x_eq_0' = x_eq_0+1
		, x_eq_1' = x_eq_1-1 ;

    p3 >= 1 , y_eq_1 >= 1 ->
		    p1' = p1+1
		, p3' = p3-1 ;

    x_eq_0 >= 1 , q3 >= 1 ->
		    q1' = q1+1
		, q3' = q3-1 ;

    q1 >= 1 ->
		    y_eq_1' = y_eq_1+1
		, q1' = q1-1
		, q2' = q2+1 ;

    x_eq_1 >= 1 , q2 >= 1 ->
		    q2' = q2-1
		, q5' = q5+1 ;

    x_eq_1 >= 1 , q3 >= 1 ->
		    q3' = q3-1
		, q4' = q4+1 ;

    q4 >= 1 ->
		    y_eq_1' = y_eq_1+1
		, q4' = q4-1
		, q5' = q5+1 ;

    y_eq_1 >= 1 , q5 >= 1 ->
		    y_eq_1' = y_eq_1-1
		, q3' = q3+1
		, q5' = q5-1 ;


init
    p1 = 0 , p2 = 1 , p3 = 0 , x_eq_0 = 0 , x_eq_1 = 1 , y_eq_1 = 1 , q1 = 0 , q2 = 0 , q3
= 0 , q4 = 0 , q5 = 1

target
    p1 >= 1 , q4 >= 1
invariants
    p1=1, p2=1, p3=1
    x_eq_0=1, x_eq_1=1
    q1=1, q2=1, q3=1, q4=1, q5=1
    y_eq_1=1, q2=1, q3=1, q4=1
