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
place('x16').
place('x17').
transition(t1, ['x0'], ['x2']).
transition(t2, ['x1'], ['x5']).
transition(t3, ['x2', 'x6'], ['x3']).
transition(t4, ['x3'], ['x0', 'x7']).
transition(t5, ['x4'], ['x1', 'x7']).
transition(t6, ['x5', 'x8'], ['x4']).
transition(t7, ['x6'], ['x7']).
transition(t8, ['x8'], ['x7']).
transition(t9, ['x9'], ['x6']).
transition(t10, ['x7'], ['x9']).
transition(t11, ['x9'], ['x8']).
transition(t12, ['x9'], ['x10']).
transition(t13, ['x9'], ['x11']).
transition(t14, ['x10'], ['x7']).
transition(t15, ['x11'], ['x7']).
transition(t16, ['x10', 'x12'], ['x13']).
transition(t17, ['x13'], ['x7', 'x16']).
transition(t18, ['x14'], ['x7', 'x17']).
transition(t19, ['x11', 'x15'], ['x14']).
transition(t20, ['x16'], ['x12']).
transition(t21, ['x17'], ['x15']).
init('x0', 1).
transition(init1, [], ['x0']).
init('x1', 1).
transition(init2, [], ['x1']).
init('x7', 3).
init('x16', 1).
transition(init3, [], ['x16']).
init('x17', 1).
transition(init4, [], ['x17']).
target(1, [(['x3'],1),(['x4'],1),(['x13'],1),(['x14'],1)]).
