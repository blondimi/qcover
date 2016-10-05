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
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l1', 's0'], ['s1', 'l2']).
transition(t4, ['l2', 's0'], ['s0', 'l3']).
transition(t5, ['l4', 's0'], ['s4', 'l5']).
transition(t6, ['l7', 's0'], ['s0', 'l8']).
transition(t7, ['l8', 's0'], ['s1', 'l9']).
transition(t8, ['l9', 's0'], ['s8', 'l17']).
transition(t9, ['l10', 's0'], ['s4', 'l11']).
transition(t10, ['l14', 's0'], ['s0', 'l2']).
transition(t11, ['l15', 's0'], ['s0', 'l16']).
transition(t12, ['l0', 's1'], ['s0', 'l1']).
transition(t13, ['l0', 's1'], ['s1', 'l1']).
transition(t14, ['l1', 's1'], ['s1', 'l2']).
transition(t15, ['l2', 's1'], ['s1', 'l3']).
transition(t16, ['l4', 's1'], ['s5', 'l5']).
transition(t17, ['l7', 's1'], ['s0', 'l8']).
transition(t18, ['l8', 's1'], ['s1', 'l9']).
transition(t19, ['l9', 's1'], ['s1', 'l10']).
transition(t20, ['l10', 's1'], ['s5', 'l11']).
transition(t21, ['l14', 's1'], ['s1', 'l2']).
transition(t22, ['l15', 's1'], ['s1', 'l16']).
transition(t23, ['l3', 's2'], ['s0', 'l14']).
transition(t24, ['l3', 's3'], ['s1', 'l14']).
transition(t25, ['l5', 's4'], ['s4', 'l6']).
transition(t26, ['l6', 's4'], ['s0', 'l7']).
transition(t27, ['l11', 's4'], ['s4', 'l12']).
transition(t28, ['l12', 's4'], ['s0', 'l13']).
transition(t29, ['l5', 's5'], ['s5', 'l6']).
transition(t30, ['l6', 's5'], ['s1', 'l7']).
transition(t31, ['l11', 's5'], ['s5', 'l12']).
transition(t32, ['l12', 's5'], ['s1', 'l13']).
transition(t33, ['l3', 's0'], ['l3', 's2', 'l4']).
transition(t34, ['l3', 's1'], ['l3', 's3', 'l4']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s8'],1),(['l17'],1)]).
