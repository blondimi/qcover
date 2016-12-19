place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
place('s6').
place('s7').
place('s8').
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
place('l14').
place('l15').
place('l16').
place('l17').
place('l18').
place('l19').
place('l20').
place('l21').
place('l22').
place('l23').
place('l24').
place('l25').
place('l26').
place('l27').
place('l28').
place('l29').
place('l30').
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l1', 's0'], ['s1', 'l2']).
transition(t4, ['l3', 's0'], ['s0', 'l4']).
transition(t5, ['l4', 's0'], ['s8', 'l30']).
transition(t6, ['l5', 's0'], ['s0', 'l3']).
transition(t7, ['l6', 's0'], ['s0', 'l7']).
transition(t8, ['l8', 's0'], ['s0', 'l9']).
transition(t9, ['l10', 's0'], ['s0', 'l11']).
transition(t10, ['l10', 's0'], ['s0', 'l12']).
transition(t11, ['l11', 's0'], ['s0', 'l13']).
transition(t12, ['l12', 's0'], ['s0', 'l13']).
transition(t13, ['l13', 's0'], ['s4', 'l14']).
transition(t14, ['l16', 's0'], ['s0', 'l17']).
transition(t15, ['l16', 's0'], ['s0', 'l18']).
transition(t16, ['l17', 's0'], ['s0', 'l18']).
transition(t17, ['l17', 's0'], ['s0', 'l21']).
transition(t18, ['l18', 's0'], ['s0', 'l19']).
transition(t19, ['l19', 's0'], ['s0', 'l20']).
transition(t20, ['l19', 's0'], ['s1', 'l20']).
transition(t21, ['l20', 's0'], ['s0', 'l23']).
transition(t22, ['l21', 's0'], ['s0', 'l22']).
transition(t23, ['l22', 's0'], ['s0', 'l23']).
transition(t24, ['l22', 's0'], ['s1', 'l23']).
transition(t25, ['l23', 's0'], ['s4', 'l24']).
transition(t26, ['l27', 's0'], ['s0', 'l8']).
transition(t27, ['l28', 's0'], ['s0', 'l29']).
transition(t28, ['l0', 's1'], ['s0', 'l1']).
transition(t29, ['l0', 's1'], ['s1', 'l1']).
transition(t30, ['l1', 's1'], ['s1', 'l2']).
transition(t31, ['l3', 's1'], ['s1', 'l4']).
transition(t32, ['l4', 's1'], ['s1', 'l5']).
transition(t33, ['l5', 's1'], ['s1', 'l3']).
transition(t34, ['l6', 's1'], ['s1', 'l7']).
transition(t35, ['l8', 's1'], ['s1', 'l9']).
transition(t36, ['l10', 's1'], ['s1', 'l11']).
transition(t37, ['l10', 's1'], ['s1', 'l12']).
transition(t38, ['l11', 's1'], ['s1', 'l13']).
transition(t39, ['l12', 's1'], ['s1', 'l13']).
transition(t40, ['l13', 's1'], ['s5', 'l14']).
transition(t41, ['l16', 's1'], ['s1', 'l17']).
transition(t42, ['l16', 's1'], ['s1', 'l18']).
transition(t43, ['l17', 's1'], ['s1', 'l18']).
transition(t44, ['l17', 's1'], ['s1', 'l21']).
transition(t45, ['l18', 's1'], ['s1', 'l19']).
transition(t46, ['l19', 's1'], ['s0', 'l20']).
transition(t47, ['l19', 's1'], ['s1', 'l20']).
transition(t48, ['l20', 's1'], ['s1', 'l23']).
transition(t49, ['l21', 's1'], ['s1', 'l22']).
transition(t50, ['l22', 's1'], ['s0', 'l23']).
transition(t51, ['l22', 's1'], ['s1', 'l23']).
transition(t52, ['l23', 's1'], ['s5', 'l24']).
transition(t53, ['l27', 's1'], ['s1', 'l8']).
transition(t54, ['l28', 's1'], ['s1', 'l29']).
transition(t55, ['l2', 's2'], ['s0', 'l8']).
transition(t56, ['l9', 's2'], ['s0', 'l27']).
transition(t57, ['l2', 's3'], ['s1', 'l8']).
transition(t58, ['l9', 's3'], ['s1', 'l27']).
transition(t59, ['l14', 's4'], ['s4', 'l15']).
transition(t60, ['l15', 's4'], ['s0', 'l16']).
transition(t61, ['l24', 's4'], ['s4', 'l25']).
transition(t62, ['l25', 's4'], ['s0', 'l26']).
transition(t63, ['l14', 's5'], ['s5', 'l15']).
transition(t64, ['l15', 's5'], ['s1', 'l16']).
transition(t65, ['l24', 's5'], ['s5', 'l25']).
transition(t66, ['l25', 's5'], ['s1', 'l26']).
transition(t67, ['l2', 's0'], ['l2', 's2', 'l3']).
transition(t68, ['l9', 's0'], ['l9', 's2', 'l10']).
transition(t69, ['l2', 's1'], ['l2', 's3', 'l3']).
transition(t70, ['l9', 's1'], ['l9', 's3', 'l10']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s8'],1),(['l30'],1)]).
