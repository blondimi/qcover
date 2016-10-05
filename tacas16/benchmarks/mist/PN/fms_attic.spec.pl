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
place('x18').
place('x19').
place('x20').
place('x21').
transition(t1, ['x0'], ['x4']).
transition(t2, ['x1', 'x11'], ['x5']).
transition(t3, ['x2'], ['x6']).
transition(t4, ['x3'], ['x7']).
transition(t5, ['x4', 'x8'], ['x9']).
transition(t6, ['x15'], ['x1']).
transition(t7, ['x5'], ['x10']).
transition(t8, ['x6', 'x13'], ['x12']).
transition(t9, ['x7', 'x13'], ['x13', 'x14']).
transition(t10, ['x9'], ['x8', 'x15']).
transition(t11, ['x10', 'x16'], ['x17']).
transition(t12, ['x18'], ['x11']).
transition(t13, ['x12'], ['x13', 'x18']).
transition(t14, ['x14'], ['x3']).
transition(t15, ['x15'], ['x19']).
transition(t16, ['x17'], ['x16', 'x20']).
transition(t17, ['x18'], ['x21']).
transition(t18, ['x19'], ['x0']).
transition(t19, ['x20'], ['x0', 'x2']).
transition(t20, ['x21'], ['x2']).
init('x0', 1).
transition(init1, [], ['x0']).
init('x2', 1).
transition(init2, [], ['x2']).
init('x3', 1).
transition(init3, [], ['x3']).
init('x8', 3).
init('x13', 1).
init('x16', 2).
target(1, [(['x9'],4)]).
target(2, [(['x12'],2)]).
