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
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l1', 's0'], ['s1', 'l2']).
transition(t4, ['l2', 's0'], ['s0', 'l3']).
transition(t5, ['l3', 's0'], ['s0', 'l4']).
transition(t6, ['l5', 's0'], ['s0', 'l6']).
transition(t7, ['l6', 's0'], ['s4', 'l7']).
transition(t8, ['l9', 's0'], ['s0', 'l10']).
transition(t9, ['l10', 's0'], ['s0', 'l9']).
transition(t10, ['l10', 's0'], ['s0', 'l11']).
transition(t11, ['l11', 's0'], ['s0', 'l12']).
transition(t12, ['l11', 's0'], ['s1', 'l12']).
transition(t13, ['l12', 's0'], ['s4', 'l13']).
transition(t14, ['l16', 's0'], ['s0', 'l3']).
transition(t15, ['l17', 's0'], ['s0', 'l18']).
transition(t16, ['l0', 's1'], ['s0', 'l1']).
transition(t17, ['l0', 's1'], ['s1', 'l1']).
transition(t18, ['l1', 's1'], ['s1', 'l2']).
transition(t19, ['l2', 's1'], ['s0', 'l3']).
transition(t20, ['l3', 's1'], ['s1', 'l4']).
transition(t21, ['l5', 's1'], ['s8', 'l19']).
transition(t22, ['l6', 's1'], ['s5', 'l7']).
transition(t23, ['l9', 's1'], ['s1', 'l10']).
transition(t24, ['l10', 's1'], ['s1', 'l9']).
transition(t25, ['l10', 's1'], ['s1', 'l11']).
transition(t26, ['l11', 's1'], ['s0', 'l12']).
transition(t27, ['l11', 's1'], ['s1', 'l12']).
transition(t28, ['l12', 's1'], ['s5', 'l13']).
transition(t29, ['l16', 's1'], ['s1', 'l3']).
transition(t30, ['l17', 's1'], ['s1', 'l18']).
transition(t31, ['l4', 's2'], ['s0', 'l16']).
transition(t32, ['l4', 's3'], ['s1', 'l16']).
transition(t33, ['l7', 's4'], ['s4', 'l8']).
transition(t34, ['l8', 's4'], ['s0', 'l9']).
transition(t35, ['l13', 's4'], ['s4', 'l14']).
transition(t36, ['l14', 's4'], ['s0', 'l15']).
transition(t37, ['l7', 's5'], ['s5', 'l8']).
transition(t38, ['l8', 's5'], ['s1', 'l9']).
transition(t39, ['l13', 's5'], ['s5', 'l14']).
transition(t40, ['l14', 's5'], ['s1', 'l15']).
transition(t41, ['l4', 's0'], ['l4', 's2', 'l5']).
transition(t42, ['l4', 's1'], ['l4', 's3', 'l5']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s8'],1),(['l19'],1)]).
