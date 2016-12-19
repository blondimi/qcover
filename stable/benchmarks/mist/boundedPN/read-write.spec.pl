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
transition(t1, ['x0'], ['x1']).
transition(t2, ['x1', 'x4'], ['x0', 'x3']).
transition(t3, ['x2', 'x11'], ['x1']).
transition(t4, ['x1'], ['x2', 'x5', 'x9']).
transition(t5, ['x6'], ['x7']).
transition(t6, ['x3', 'x7'], ['x4', 'x6']).
transition(t7, ['x8', 'x12'], [('x4', 5), 'x7']).
transition(t8, [('x4', 5), 'x5', 'x7'], ['x8', 'x10']).
transition(t9, ['x9', 'x10'], ['x11', 'x12']).
init('x2', 1).
init('x8', 1).
init('x11', 1).
init('x12', 1).
target(1, [(['x3'],1),(['x10'],1)]).
