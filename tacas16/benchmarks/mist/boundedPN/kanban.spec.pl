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
place('x14').
place('x15').
transition(t1, ['x2'], ['x0']).
transition(t2, ['x0'], ['x1']).
transition(t3, ['x1'], ['x0']).
transition(t4, ['x0'], ['x3']).
transition(t5, ['x3', 'x6', 'x10'], ['x2', 'x4', 'x8']).
transition(t6, ['x4'], ['x5']).
transition(t7, ['x5'], ['x4']).
transition(t8, ['x4'], ['x7']).
transition(t9, ['x7', 'x11', 'x14'], ['x6', 'x10', 'x12']).
transition(t10, ['x8'], ['x9']).
transition(t11, ['x9'], ['x8']).
transition(t12, ['x8'], ['x11']).
transition(t13, ['x12'], ['x13']).
transition(t14, ['x13'], ['x12']).
transition(t15, ['x12'], ['x15']).
transition(t16, ['x15'], ['x14']).
init('x2', 1).
init('x6', 1).
init('x10', 1).
init('x14', 1).
target(1, [(['x4'],2),(['x6'],4),(['x10'],4),(['x13'],6),(['x14'],4)]).
