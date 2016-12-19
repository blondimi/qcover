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
place('x12').
place('x13').
transition(t1, ['x0', 'x4'], ['x1', 'x5']).
transition(t2, ['x1', 'x6'], ['x2', 'x7']).
transition(t3, ['x1', 'x7'], ['x7', 'x2']).
transition(t4, ['x2', 'x9'], ['x9', 'x3']).
transition(t5, ['x2', 'x6'], ['x6', 'x3']).
transition(t6, ['x3', 'x5'], ['x0', 'x4']).
transition(t7, ['x9', 'x10'], ['x8', 'x11']).
transition(t8, ['x7', 'x11'], ['x6', 'x12']).
transition(t9, ['x6', 'x11'], ['x6', 'x12']).
transition(t10, ['x4', 'x12'], ['x4', 'x13']).
transition(t11, ['x7', 'x12'], ['x7', 'x13']).
transition(t12, ['x8', 'x13'], ['x9', 'x10']).
init('x0', 1).
init('x4', 1).
init('x7', 1).
init('x9', 1).
init('x10', 1).
target(1, [(['x3'],1),(['x13'],1)]).
