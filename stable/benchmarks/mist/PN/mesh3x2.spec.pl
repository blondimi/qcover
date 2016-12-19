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
place('x32').
place('x33').
place('x34').
place('x35').
place('x36').
place('x37').
place('x38').
place('x39').
place('x40').
place('x41').
place('x42').
place('x43').
place('x44').
place('x45').
place('x46').
place('x47').
place('x48').
place('x49').
place('x50').
place('x51').
transition(t1, ['x0', 'x3'], ['x1']).
transition(t2, ['x1'], ['x2', 'x3']).
transition(t3, ['x3', 'x13'], ['x4']).
transition(t4, ['x3', 'x30'], ['x5']).
transition(t5, ['x4'], ['x3', 'x8']).
transition(t6, ['x5'], ['x3', 'x32']).
transition(t7, ['x2'], ['x6']).
transition(t8, ['x2'], ['x7']).
transition(t9, ['x8', 'x14'], ['x9']).
transition(t10, ['x9'], ['x10', 'x14']).
transition(t11, ['x10'], ['x11']).
transition(t12, ['x10'], ['x12']).
transition(t13, ['x10'], ['x13']).
transition(t14, ['x14', 'x39'], ['x15']).
transition(t15, ['x7', 'x14'], ['x16']).
transition(t16, ['x14', 'x25'], ['x17']).
transition(t17, ['x15'], ['x0', 'x14']).
transition(t18, ['x16'], ['x14', 'x36']).
transition(t19, ['x17'], ['x14', 'x23']).
transition(t20, ['x11', 'x21'], ['x18']).
transition(t21, ['x18'], ['x8', 'x21']).
transition(t22, ['x19'], ['x21', 'x44']).
transition(t23, ['x20'], ['x21', 'x32']).
transition(t24, ['x21', 'x47'], ['x19']).
transition(t25, ['x21', 'x29'], ['x20']).
transition(t26, ['x21', 'x23'], ['x22']).
transition(t27, ['x22'], ['x21', 'x24']).
transition(t28, ['x24'], ['x26']).
transition(t29, ['x24'], ['x25']).
transition(t30, ['x24'], ['x27']).
transition(t31, ['x31'], ['x28', 'x33']).
transition(t32, ['x28'], ['x30']).
transition(t33, ['x28'], ['x29']).
transition(t34, ['x32', 'x33'], ['x31']).
transition(t35, ['x27', 'x33'], ['x34']).
transition(t36, ['x6', 'x33'], ['x35']).
transition(t37, ['x34'], ['x23', 'x33']).
transition(t38, ['x35'], ['x0', 'x33']).
transition(t39, ['x36', 'x41'], ['x37']).
transition(t40, ['x37'], ['x38', 'x41']).
transition(t41, ['x38'], ['x39']).
transition(t42, ['x38'], ['x40']).
transition(t43, ['x12', 'x41'], ['x42']).
transition(t44, ['x41', 'x48'], ['x43']).
transition(t45, ['x42'], ['x8', 'x41']).
transition(t46, ['x43'], ['x41', 'x44']).
transition(t47, ['x44', 'x49'], ['x45']).
transition(t48, ['x45'], ['x46', 'x49']).
transition(t49, ['x46'], ['x48']).
transition(t50, ['x46'], ['x47']).
transition(t51, ['x26', 'x49'], ['x50']).
transition(t52, ['x40', 'x49'], ['x51']).
transition(t53, ['x50'], ['x23', 'x49']).
transition(t54, ['x51'], ['x36', 'x49']).
init('x0', 1).
transition(init1, [], ['x0']).
init('x3', 1).
init('x8', 1).
transition(init2, [], ['x8']).
init('x14', 1).
init('x21', 1).
init('x23', 1).
transition(init3, [], ['x23']).
init('x32', 1).
transition(init4, [], ['x32']).
init('x33', 1).
init('x36', 1).
transition(init5, [], ['x36']).
init('x41', 1).
init('x44', 1).
transition(init6, [], ['x44']).
init('x49', 1).
target(1, [(['x1'],1),(['x4'],1)]).
