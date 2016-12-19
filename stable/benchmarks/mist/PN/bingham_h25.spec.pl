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
transition(t1, ['x0', 'x27'], ['x26', 'x1']).
transition(t2, ['x1', 'x27'], ['x26', 'x0']).
transition(t3, ['x1', 'x26'], ['x0', 'x27']).
transition(t4, ['x1'], ['x2']).
transition(t5, ['x2', 'x26'], ['x0', 'x27']).
transition(t6, ['x2'], ['x3']).
transition(t7, ['x3', 'x26'], ['x0', 'x27']).
transition(t8, ['x3'], ['x4']).
transition(t9, ['x4', 'x26'], ['x0', 'x27']).
transition(t10, ['x4'], ['x5']).
transition(t11, ['x5', 'x26'], ['x0', 'x27']).
transition(t12, ['x5'], ['x6']).
transition(t13, ['x6', 'x26'], ['x0', 'x27']).
transition(t14, ['x6'], ['x7']).
transition(t15, ['x7', 'x26'], ['x0', 'x27']).
transition(t16, ['x7'], ['x8']).
transition(t17, ['x8', 'x26'], ['x0', 'x27']).
transition(t18, ['x8'], ['x9']).
transition(t19, ['x9', 'x26'], ['x0', 'x27']).
transition(t20, ['x9'], ['x10']).
transition(t21, ['x10', 'x26'], ['x0', 'x27']).
transition(t22, ['x10'], ['x11']).
transition(t23, ['x11', 'x26'], ['x0', 'x27']).
transition(t24, ['x11'], ['x12']).
transition(t25, ['x12', 'x26'], ['x0', 'x27']).
transition(t26, ['x12'], ['x13']).
transition(t27, ['x13', 'x26'], ['x0', 'x27']).
transition(t28, ['x13'], ['x14']).
transition(t29, ['x14', 'x26'], ['x0', 'x27']).
transition(t30, ['x14'], ['x15']).
transition(t31, ['x15', 'x26'], ['x0', 'x27']).
transition(t32, ['x15'], ['x16']).
transition(t33, ['x16', 'x26'], ['x0', 'x27']).
transition(t34, ['x16'], ['x17']).
transition(t35, ['x17', 'x26'], ['x0', 'x27']).
transition(t36, ['x17'], ['x18']).
transition(t37, ['x18', 'x26'], ['x0', 'x27']).
transition(t38, ['x18'], ['x19']).
transition(t39, ['x19', 'x26'], ['x0', 'x27']).
transition(t40, ['x19'], ['x20']).
transition(t41, ['x20', 'x26'], ['x0', 'x27']).
transition(t42, ['x20'], ['x21']).
transition(t43, ['x21', 'x26'], ['x0', 'x27']).
transition(t44, ['x21'], ['x22']).
transition(t45, ['x22', 'x26'], ['x0', 'x27']).
transition(t46, ['x22'], ['x23']).
transition(t47, ['x23', 'x26'], ['x0', 'x27']).
transition(t48, ['x23'], ['x24']).
transition(t49, ['x24', 'x26'], ['x0', 'x27']).
transition(t50, ['x24'], ['x25']).
transition(t51, ['x25', 'x26'], ['x0', 'x27']).
init('x0', 1).
transition(init1, [], ['x0']).
init('x27', 1).
target(1, [(['x25'],2)]).
