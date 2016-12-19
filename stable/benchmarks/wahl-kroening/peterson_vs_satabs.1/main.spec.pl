place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
place('s6').
place('s7').
place('s8').
place('s9').
place('s10').
place('s11').
place('s12').
place('s13').
place('s14').
place('s15').
place('s16').
place('l0').
place('l1').
place('l2').
place('l3').
place('l4').
place('l5').
place('l6').
place('l7').
place('l8').
place('l9').
place('l10').
place('l11').
place('l12').
place('l13').
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s2', 'l1']).
transition(t3, ['l1', 's0'], ['s0', 'l2']).
transition(t4, ['l1', 's0'], ['s1', 'l2']).
transition(t5, ['l2', 's0'], ['s2', 'l3']).
transition(t6, ['l4', 's0'], ['l4', 's0']).
transition(t7, ['l4', 's0'], ['s0', 'l5']).
transition(t8, ['l5', 's0'], ['s2', 'l6']).
transition(t9, ['l6', 's0'], ['s16', 'l13']).
transition(t10, ['l8', 's0'], ['s0', 'l9']).
transition(t11, ['l9', 's0'], ['l9', 's0']).
transition(t12, ['l9', 's0'], ['s0', 'l10']).
transition(t13, ['l10', 's0'], ['s1', 'l11']).
transition(t14, ['l11', 's0'], ['s16', 'l13']).
transition(t15, ['l0', 's1'], ['s1', 'l1']).
transition(t16, ['l0', 's1'], ['s3', 'l1']).
transition(t17, ['l1', 's1'], ['s0', 'l2']).
transition(t18, ['l1', 's1'], ['s1', 'l2']).
transition(t19, ['l2', 's1'], ['s2', 'l3']).
transition(t20, ['l4', 's1'], ['l4', 's1']).
transition(t21, ['l4', 's1'], ['s1', 'l5']).
transition(t22, ['l5', 's1'], ['s2', 'l6']).
transition(t23, ['l6', 's1'], ['s16', 'l13']).
transition(t24, ['l8', 's1'], ['s1', 'l9']).
transition(t25, ['l9', 's1'], ['l9', 's1']).
transition(t26, ['l9', 's1'], ['s1', 'l10']).
transition(t27, ['l10', 's1'], ['s1', 'l11']).
transition(t28, ['l11', 's1'], ['s1', 'l12']).
transition(t29, ['l0', 's2'], ['s0', 'l1']).
transition(t30, ['l0', 's2'], ['s2', 'l1']).
transition(t31, ['l1', 's2'], ['s2', 'l2']).
transition(t32, ['l1', 's2'], ['s3', 'l2']).
transition(t33, ['l2', 's2'], ['s2', 'l3']).
transition(t34, ['l4', 's2'], ['l4', 's2']).
transition(t35, ['l4', 's2'], ['s2', 'l5']).
transition(t36, ['l5', 's2'], ['s2', 'l6']).
transition(t37, ['l6', 's2'], ['s2', 'l7']).
transition(t38, ['l8', 's2'], ['s2', 'l9']).
transition(t39, ['l9', 's2'], ['l9', 's2']).
transition(t40, ['l9', 's2'], ['s2', 'l10']).
transition(t41, ['l10', 's2'], ['s1', 'l11']).
transition(t42, ['l11', 's2'], ['s16', 'l13']).
transition(t43, ['l0', 's3'], ['s1', 'l1']).
transition(t44, ['l0', 's3'], ['s3', 'l1']).
transition(t45, ['l1', 's3'], ['s2', 'l2']).
transition(t46, ['l1', 's3'], ['s3', 'l2']).
transition(t47, ['l2', 's3'], ['s2', 'l3']).
transition(t48, ['l4', 's3'], ['l4', 's3']).
transition(t49, ['l4', 's3'], ['s3', 'l5']).
transition(t50, ['l5', 's3'], ['s2', 'l6']).
transition(t51, ['l6', 's3'], ['s3', 'l7']).
transition(t52, ['l8', 's3'], ['s3', 'l9']).
transition(t53, ['l9', 's3'], ['l9', 's3']).
transition(t54, ['l9', 's3'], ['s3', 'l10']).
transition(t55, ['l10', 's3'], ['s1', 'l11']).
transition(t56, ['l11', 's3'], ['s3', 'l12']).
transition(t57, ['l3', 's4'], ['s0', 'l8']).
transition(t58, ['l3', 's5'], ['s1', 'l8']).
transition(t59, ['l3', 's6'], ['s2', 'l8']).
transition(t60, ['l3', 's7'], ['s3', 'l8']).
transition(t61, ['l3', 's0'], ['l3', 's4', 'l4']).
transition(t62, ['l3', 's1'], ['l3', 's5', 'l4']).
transition(t63, ['l3', 's2'], ['l3', 's6', 'l4']).
transition(t64, ['l3', 's3'], ['l3', 's7', 'l4']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s16'],1),(['l13'],1)]).
