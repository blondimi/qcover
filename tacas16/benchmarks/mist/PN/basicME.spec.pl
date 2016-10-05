place('x0').
place('x1').
place('x2').
place('x3').
place('x4').
transition(t1, ['x0', 'x1', 'x2'], ['x1', 'x3']).
transition(t2, ['x0', 'x1', 'x2'], ['x2', 'x4']).
transition(t3, ['x3'], ['x0', 'x2']).
transition(t4, ['x4'], ['x0', 'x1']).
init('x0', 1).
transition(init1, [], ['x0']).
init('x1', 1).
init('x2', 1).
target(1, [(['x3'],1),(['x4'],1)]).
target(2, [(['x3'],2)]).
target(3, [(['x4'],2)]).
