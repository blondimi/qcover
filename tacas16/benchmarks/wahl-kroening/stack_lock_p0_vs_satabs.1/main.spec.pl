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
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l1', 's0'], ['s1', 'l2']).
transition(t4, ['l2', 's0'], ['s1', 'l3']).
transition(t5, ['l3', 's0'], ['s0', 'l4']).
transition(t6, ['l5', 's0'], ['s4', 'l6']).
transition(t7, ['l10', 's0'], ['s0', 'l11']).
transition(t8, ['l10', 's0'], ['s0', 'l13']).
transition(t9, ['l12', 's0'], ['s0', 'l21']).
transition(t10, ['l13', 's0'], ['s0', 'l14']).
transition(t11, ['l14', 's0'], ['s4', 'l15']).
transition(t12, ['l17', 's0'], ['s0', 'l18']).
transition(t13, ['l17', 's0'], ['s1', 'l18']).
transition(t14, ['l18', 's0'], ['s4', 'l19']).
transition(t15, ['l21', 's0'], ['s0', 'l22']).
transition(t16, ['l22', 's0'], ['s0', 'l23']).
transition(t17, ['l24', 's0'], ['s0', 'l3']).
transition(t18, ['l25', 's0'], ['s0', 'l26']).
transition(t19, ['l0', 's1'], ['s0', 'l1']).
transition(t20, ['l0', 's1'], ['s1', 'l1']).
transition(t21, ['l1', 's1'], ['s1', 'l2']).
transition(t22, ['l2', 's1'], ['s1', 'l3']).
transition(t23, ['l3', 's1'], ['s1', 'l4']).
transition(t24, ['l5', 's1'], ['s5', 'l6']).
transition(t25, ['l10', 's1'], ['s1', 'l11']).
transition(t26, ['l10', 's1'], ['s1', 'l13']).
transition(t27, ['l12', 's1'], ['s1', 'l21']).
transition(t28, ['l13', 's1'], ['s1', 'l14']).
transition(t29, ['l14', 's1'], ['s5', 'l15']).
transition(t30, ['l17', 's1'], ['s0', 'l18']).
transition(t31, ['l17', 's1'], ['s1', 'l18']).
transition(t32, ['l18', 's1'], ['s5', 'l19']).
transition(t33, ['l21', 's1'], ['s1', 'l22']).
transition(t34, ['l22', 's1'], ['s8', 'l27']).
transition(t35, ['l24', 's1'], ['s1', 'l3']).
transition(t36, ['l25', 's1'], ['s1', 'l26']).
transition(t37, ['l4', 's2'], ['s0', 'l24']).
transition(t38, ['l4', 's3'], ['s1', 'l24']).
transition(t39, ['l6', 's4'], ['s4', 'l7']).
transition(t40, ['l6', 's4'], ['s4', 'l8']).
transition(t41, ['l7', 's4'], ['s4', 'l9']).
transition(t42, ['l8', 's4'], ['s4', 'l9']).
transition(t43, ['l9', 's4'], ['s0', 'l10']).
transition(t44, ['l15', 's4'], ['s4', 'l16']).
transition(t45, ['l16', 's4'], ['s0', 'l17']).
transition(t46, ['l19', 's4'], ['s4', 'l20']).
transition(t47, ['l20', 's4'], ['s0', 'l21']).
transition(t48, ['l6', 's5'], ['s5', 'l7']).
transition(t49, ['l6', 's5'], ['s5', 'l8']).
transition(t50, ['l7', 's5'], ['s5', 'l9']).
transition(t51, ['l8', 's5'], ['s5', 'l9']).
transition(t52, ['l9', 's5'], ['s1', 'l10']).
transition(t53, ['l15', 's5'], ['s5', 'l16']).
transition(t54, ['l16', 's5'], ['s1', 'l17']).
transition(t55, ['l19', 's5'], ['s5', 'l20']).
transition(t56, ['l20', 's5'], ['s1', 'l21']).
transition(t57, ['l4', 's0'], ['l4', 's2', 'l5']).
transition(t58, ['l4', 's1'], ['l4', 's3', 'l5']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s8'],1),(['l27'],1)]).
