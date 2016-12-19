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
place('x14').
transition(t1, ['x1'], ['x2']).
transition(t2, ['x5', 'x10'], ['x1', 'x3']).
transition(t3, ['x5', 'x7'], ['x1', 'x4']).
transition(t4, ['x2', 'x4'], ['x6', 'x7']).
transition(t5, ['x2', 'x3'], ['x6', 'x10']).
transition(t6, ['x6'], ['x5']).
transition(t7, ['x11'], ['x8']).
transition(t8, ['x8'], ['x9']).
transition(t9, ['x7', 'x9'], ['x10']).
transition(t10, ['x10'], ['x7', 'x11']).
transition(t11, ['x11'], ['x13']).
transition(t12, ['x12'], ['x9', 'x14']).
transition(t13, ['x13', 'x14'], ['x12']).
init('x6', 1).
init('x7', 1).
init('x8', 1).
transition(init1, [], ['x8']).
init('x14', 1).
target(1, [(['x10'],2)]).
