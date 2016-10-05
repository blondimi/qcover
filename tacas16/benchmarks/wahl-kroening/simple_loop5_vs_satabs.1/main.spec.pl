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
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l1', 's0'], ['s0', 'l2']).
transition(t4, ['l1', 's0'], ['s1', 'l2']).
transition(t5, ['l2', 's0'], ['s0', 'l3']).
transition(t6, ['l2', 's0'], ['s1', 'l3']).
transition(t7, ['l4', 's0'], ['s0', 'l5']).
transition(t8, ['l5', 's0'], ['s4', 'l6']).
transition(t9, ['l8', 's0'], ['s0', 'l9']).
transition(t10, ['l9', 's0'], ['s4', 'l10']).
transition(t11, ['l12', 's0'], ['s0', 'l4']).
transition(t12, ['l13', 's0'], ['s0', 'l14']).
transition(t13, ['l15', 's0'], ['s0', 'l16']).
transition(t14, ['l17', 's0'], ['l17', 's0']).
transition(t15, ['l18', 's0'], ['s0', 'l15']).
transition(t16, ['l19', 's0'], ['s0', 'l20']).
transition(t17, ['l0', 's1'], ['s0', 'l1']).
transition(t18, ['l0', 's1'], ['s1', 'l1']).
transition(t19, ['l1', 's1'], ['s0', 'l2']).
transition(t20, ['l1', 's1'], ['s1', 'l2']).
transition(t21, ['l2', 's1'], ['s0', 'l3']).
transition(t22, ['l2', 's1'], ['s1', 'l3']).
transition(t23, ['l4', 's1'], ['s1', 'l5']).
transition(t24, ['l5', 's1'], ['s5', 'l6']).
transition(t25, ['l8', 's1'], ['s8', 'l21']).
transition(t26, ['l9', 's1'], ['s5', 'l10']).
transition(t27, ['l12', 's1'], ['s1', 'l4']).
transition(t28, ['l13', 's1'], ['s1', 'l14']).
transition(t29, ['l15', 's1'], ['s1', 'l16']).
transition(t30, ['l17', 's1'], ['l17', 's1']).
transition(t31, ['l18', 's1'], ['s1', 'l15']).
transition(t32, ['l19', 's1'], ['s1', 'l20']).
transition(t33, ['l3', 's2'], ['s0', 'l15']).
transition(t34, ['l16', 's2'], ['s0', 'l18']).
transition(t35, ['l3', 's3'], ['s1', 'l15']).
transition(t36, ['l16', 's3'], ['s1', 'l18']).
transition(t37, ['l6', 's4'], ['s4', 'l7']).
transition(t38, ['l7', 's4'], ['s0', 'l8']).
transition(t39, ['l10', 's4'], ['s4', 'l11']).
transition(t40, ['l11', 's4'], ['s0', 'l12']).
transition(t41, ['l6', 's5'], ['s5', 'l7']).
transition(t42, ['l7', 's5'], ['s1', 'l8']).
transition(t43, ['l10', 's5'], ['s5', 'l11']).
transition(t44, ['l11', 's5'], ['s1', 'l12']).
transition(t45, ['l3', 's0'], ['l3', 's2', 'l4']).
transition(t46, ['l16', 's0'], ['l16', 's2', 'l17']).
transition(t47, ['l3', 's1'], ['l3', 's3', 'l4']).
transition(t48, ['l16', 's1'], ['l16', 's3', 'l17']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s8'],1),(['l21'],1)]).
