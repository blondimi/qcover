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
transition(t1, ['x2'], ['x3', 'x21']).
transition(t2, ['x3', 'x22'], ['x4', 'x23']).
transition(t3, ['x4', 'x24'], ['x5', 'x25']).
transition(t4, ['x5', 'x27'], ['x6']).
transition(t5, ['x6'], ['x7', 'x29']).
transition(t6, ['x7'], ['x9']).
transition(t7, ['x9', 'x11'], ['x1', 'x2']).
transition(t8, ['x7', 'x30'], ['x6']).
transition(t9, ['x6'], ['x8', 'x28']).
transition(t10, ['x8'], ['x9']).
transition(t11, ['x9'], ['x0', 'x10']).
transition(t12, ['x8', 'x26'], ['x0', 'x10']).
transition(t13, ['x4'], ['x0', 'x10']).
transition(t14, ['x3'], ['x0', 'x10']).
transition(t15, ['x10', 'x12'], ['x2']).
transition(t16, ['x10', 'x11'], ['x2']).
transition(t17, ['x10'], ['x2']).
transition(t18, ['x10'], ['x10', 'x0']).
transition(t19, ['x13', 'x21'], ['x14', 'x22']).
transition(t20, ['x14', 'x23'], ['x15', 'x24']).
transition(t21, ['x15', 'x25'], ['x16', 'x27']).
transition(t22, ['x16', 'x29'], ['x17']).
transition(t23, ['x17'], ['x18']).
transition(t24, ['x18'], ['x19']).
transition(t25, ['x0', 'x19'], ['x12', 'x13']).
transition(t26, ['x17'], ['x16', 'x30']).
transition(t27, ['x16'], ['x19']).
transition(t28, ['x16', 'x28'], ['x19', 'x26']).
transition(t29, ['x15'], ['x11', 'x20']).
transition(t30, ['x19'], ['x11', 'x20']).
transition(t31, ['x18'], ['x11', 'x20']).
transition(t32, ['x14'], ['x11', 'x20']).
transition(t33, ['x1', 'x20'], ['x13']).
transition(t34, ['x0', 'x20'], ['x13']).
transition(t35, ['x20'], ['x13']).
transition(t36, ['x20'], ['x20', 'x11']).
init('x2', 1).
init('x13', 1).
target(1, [(['x12'],1),(['x21'],1),(['x23'],1),(['x28'],1),(['x30'],1)]).
