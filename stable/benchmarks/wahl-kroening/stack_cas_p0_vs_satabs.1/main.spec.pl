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
place('l31').
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l1', 's0'], ['s1', 'l2']).
transition(t4, ['l2', 's0'], ['s1', 'l3']).
transition(t5, ['l3', 's0'], ['s0', 'l4']).
transition(t6, ['l5', 's0'], ['s0', 'l6']).
transition(t7, ['l6', 's0'], ['s4', 'l7']).
transition(t8, ['l11', 's0'], ['s0', 'l12']).
transition(t9, ['l11', 's0'], ['s0', 'l13']).
transition(t10, ['l13', 's0'], ['s0', 'l14']).
transition(t11, ['l14', 's0'], ['s0', 'l15']).
transition(t12, ['l15', 's0'], ['s4', 'l16']).
transition(t13, ['l21', 's0'], ['s0', 'l22']).
transition(t14, ['l21', 's0'], ['s0', 'l23']).
transition(t15, ['l22', 's0'], ['s0', 'l24']).
transition(t16, ['l23', 's0'], ['s0', 'l14']).
transition(t17, ['l24', 's0'], ['s0', 'l25']).
transition(t18, ['l25', 's0'], ['s0', 'l26']).
transition(t19, ['l26', 's0'], ['s0', 'l5']).
transition(t20, ['l28', 's0'], ['s0', 'l3']).
transition(t21, ['l29', 's0'], ['s0', 'l30']).
transition(t22, ['l0', 's1'], ['s0', 'l1']).
transition(t23, ['l0', 's1'], ['s1', 'l1']).
transition(t24, ['l1', 's1'], ['s1', 'l2']).
transition(t25, ['l2', 's1'], ['s1', 'l3']).
transition(t26, ['l3', 's1'], ['s1', 'l4']).
transition(t27, ['l5', 's1'], ['s1', 'l6']).
transition(t28, ['l6', 's1'], ['s5', 'l7']).
transition(t29, ['l11', 's1'], ['s1', 'l12']).
transition(t30, ['l11', 's1'], ['s1', 'l13']).
transition(t31, ['l13', 's1'], ['s1', 'l14']).
transition(t32, ['l14', 's1'], ['s1', 'l15']).
transition(t33, ['l15', 's1'], ['s5', 'l16']).
transition(t34, ['l21', 's1'], ['s1', 'l22']).
transition(t35, ['l21', 's1'], ['s1', 'l23']).
transition(t36, ['l22', 's1'], ['s1', 'l24']).
transition(t37, ['l23', 's1'], ['s1', 'l14']).
transition(t38, ['l24', 's1'], ['s1', 'l25']).
transition(t39, ['l25', 's1'], ['s8', 'l31']).
transition(t40, ['l26', 's1'], ['s1', 'l5']).
transition(t41, ['l28', 's1'], ['s1', 'l3']).
transition(t42, ['l29', 's1'], ['s1', 'l30']).
transition(t43, ['l4', 's2'], ['s0', 'l28']).
transition(t44, ['l4', 's3'], ['s1', 'l28']).
transition(t45, ['l7', 's4'], ['s4', 'l8']).
transition(t46, ['l7', 's4'], ['s4', 'l9']).
transition(t47, ['l8', 's4'], ['s4', 'l10']).
transition(t48, ['l9', 's4'], ['s4', 'l10']).
transition(t49, ['l10', 's4'], ['s0', 'l11']).
transition(t50, ['l16', 's4'], ['s4', 'l17']).
transition(t51, ['l16', 's4'], ['s4', 'l19']).
transition(t52, ['l17', 's4'], ['s4', 'l18']).
transition(t53, ['l17', 's4'], ['s5', 'l18']).
transition(t54, ['l18', 's4'], ['s4', 'l20']).
transition(t55, ['l19', 's4'], ['s4', 'l20']).
transition(t56, ['l20', 's4'], ['s0', 'l21']).
transition(t57, ['l7', 's5'], ['s5', 'l8']).
transition(t58, ['l7', 's5'], ['s5', 'l9']).
transition(t59, ['l8', 's5'], ['s5', 'l10']).
transition(t60, ['l9', 's5'], ['s5', 'l10']).
transition(t61, ['l10', 's5'], ['s1', 'l11']).
transition(t62, ['l16', 's5'], ['s5', 'l17']).
transition(t63, ['l16', 's5'], ['s5', 'l19']).
transition(t64, ['l17', 's5'], ['s4', 'l18']).
transition(t65, ['l17', 's5'], ['s5', 'l18']).
transition(t66, ['l18', 's5'], ['s5', 'l20']).
transition(t67, ['l19', 's5'], ['s5', 'l20']).
transition(t68, ['l20', 's5'], ['s1', 'l21']).
transition(t69, ['l4', 's0'], ['l4', 's2', 'l5']).
transition(t70, ['l4', 's1'], ['l4', 's3', 'l5']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s8'],1),(['l31'],1)]).
