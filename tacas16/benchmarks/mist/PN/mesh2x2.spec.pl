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
place('x22').
place('x23').
place('x24').
place('x25').
place('x26').
place('x27').
place('x28').
place('x29').
place('x30').
place('x31').
transition(t1, ['x0', 'x3'], ['x2']).
transition(t2, ['x1', 'x4'], ['x5']).
transition(t3, ['x3', 'x28'], ['x6']).
transition(t4, ['x3', 'x14'], ['x7']).
transition(t5, ['x4', 'x13'], ['x8']).
transition(t6, ['x4', 'x31'], ['x9']).
transition(t7, ['x2'], ['x3', 'x10']).
transition(t8, ['x5'], ['x4', 'x11']).
transition(t9, ['x6'], ['x3', 'x16']).
transition(t10, ['x7'], ['x1', 'x3']).
transition(t11, ['x8'], ['x0', 'x4']).
transition(t12, ['x9'], ['x4', 'x17']).
transition(t13, ['x10'], ['x12']).
transition(t14, ['x10'], ['x13']).
transition(t15, ['x11'], ['x14']).
transition(t16, ['x11'], ['x15']).
transition(t17, ['x16', 'x19'], ['x18']).
transition(t18, ['x17', 'x20'], ['x21']).
transition(t19, ['x12', 'x19'], ['x22']).
transition(t20, ['x19', 'x30'], ['x23']).
transition(t21, ['x20', 'x29'], ['x24']).
transition(t22, ['x15', 'x20'], ['x25']).
transition(t23, ['x18'], ['x19', 'x26']).
transition(t24, ['x21'], ['x20', 'x27']).
transition(t25, ['x22'], ['x0', 'x19']).
transition(t26, ['x23'], ['x17', 'x19']).
transition(t27, ['x24'], ['x16', 'x20']).
transition(t28, ['x25'], ['x1', 'x20']).
transition(t29, ['x26'], ['x28']).
transition(t30, ['x26'], ['x29']).
transition(t31, ['x27'], ['x30']).
transition(t32, ['x27'], ['x31']).
init('x0', 1).
transition(init1, [], ['x0']).
init('x1', 1).
transition(init2, [], ['x1']).
init('x3', 1).
init('x4', 1).
init('x16', 1).
transition(init3, [], ['x16']).
init('x17', 1).
transition(init4, [], ['x17']).
init('x19', 1).
init('x20', 1).
target(1, [(['x2'],1),(['x7'],1)]).
