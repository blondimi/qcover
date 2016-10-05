place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
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
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s0', 'l2']).
transition(t3, ['l1', 's0'], ['s0', 'l5']).
transition(t4, ['l2', 's0'], ['s0', 'l3']).
transition(t5, ['l3', 's0'], ['s2', 'l4']).
transition(t6, ['l5', 's0'], ['s0', 'l6']).
transition(t7, ['l6', 's0'], ['s0', 'l7']).
transition(t8, ['l7', 's0'], ['s0', 'l8']).
transition(t9, ['l7', 's0'], ['s0', 'l9']).
transition(t10, ['l8', 's0'], ['s0', 'l6']).
transition(t11, ['l9', 's0'], ['s0', 'l10']).
transition(t12, ['l10', 's0'], ['s0', 'l11']).
transition(t13, ['l10', 's0'], ['s0', 'l12']).
transition(t14, ['l11', 's0'], ['s0', 'l15']).
transition(t15, ['l12', 's0'], ['s0', 'l13']).
transition(t16, ['l13', 's0'], ['s2', 'l14']).
transition(t17, ['l15', 's0'], ['s0', 'l16']).
transition(t18, ['l16', 's0'], ['s0', 'l17']).
transition(t19, ['l16', 's0'], ['s0', 'l18']).
transition(t20, ['l17', 's0'], ['s0', 'l19']).
transition(t21, ['l18', 's0'], ['s0', 'l19']).
transition(t22, ['l19', 's0'], ['s0', 'l9']).
transition(t23, ['l19', 's0'], ['s0', 'l20']).
transition(t24, ['l20', 's0'], ['s0', 'l21']).
transition(t25, ['l20', 's0'], ['s0', 'l23']).
transition(t26, ['l21', 's0'], ['s4', 'l25']).
transition(t27, ['l22', 's0'], ['l22', 's0']).
transition(t28, ['l23', 's0'], ['l23', 's0']).
transition(t29, ['l4', 's2'], ['s0', 'l5']).
transition(t30, ['l14', 's2'], ['s0', 'l15']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s4'],1),(['l25'],1)]).
