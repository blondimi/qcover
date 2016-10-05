place('x0').
place('x1').
place('x2').
place('x3').
place('x4').
place('x5').
place('x6').
place('x7').
place('x8').
place('x9').
place('x10').
place('x11').
transition(t1, ['x0', 'x1', 'x2'], ['x1', 'x3']).
transition(t2, ['x0', 'x1', 'x2'], ['x2', 'x4']).
transition(t3, ['x3'], ['x0', 'x2']).
transition(t4, ['x4'], ['x0', 'x1']).
transition(t5, ['x0', 'x5', 'x6'], ['x5', 'x7']).
transition(t6, ['x0', 'x5', 'x6'], ['x6', 'x8']).
transition(t7, ['x7'], ['x0', 'x6']).
transition(t8, ['x8'], ['x0', 'x5']).
transition(t9, ['x9'], ['x10']).
transition(t10, ['x10'], ['x11']).
transition(t11, ['x11'], ['x10', 'x0']).
init('x1', 1).
init('x2', 1).
init('x5', 1).
init('x6', 1).
init('x9', 1).
target(1, [(['x3'],1),(['x4'],1)]).
target(2, [(['x3'],2)]).
target(3, [(['x4'],2)]).
