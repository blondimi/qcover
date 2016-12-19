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
place('l26').
place('l27').
place('l28').
place('l29').
place('l30').
place('l31').
place('l32').
place('l33').
transition(t1, ['l1', 's0'], ['s2', 'l2']).
transition(t2, ['l4', 's0'], ['s2', 'l5']).
transition(t3, ['l9', 's0'], ['s2', 'l10']).
transition(t4, ['l12', 's0'], ['s0', 'l13']).
transition(t5, ['l12', 's0'], ['s0', 'l14']).
transition(t6, ['l13', 's0'], ['s0', 'l16']).
transition(t7, ['l14', 's0'], ['s0', 'l15']).
transition(t8, ['l15', 's0'], ['s0', 'l16']).
transition(t9, ['l16', 's0'], ['s0', 'l17']).
transition(t10, ['l18', 's0'], ['s0', 'l19']).
transition(t11, ['l19', 's0'], ['s0', 'l20']).
transition(t12, ['l19', 's0'], ['s0', 'l21']).
transition(t13, ['l20', 's0'], ['s0', 'l19']).
transition(t14, ['l21', 's0'], ['s2', 'l22']).
transition(t15, ['l24', 's0'], ['s2', 'l25']).
transition(t16, ['l27', 's0'], ['s2', 'l28']).
transition(t17, ['l0', 's1'], ['s0', 'l18']).
transition(t18, ['l2', 's2'], ['s2', 'l3']).
transition(t19, ['l3', 's2'], ['s0', 'l4']).
transition(t20, ['l5', 's2'], ['s2', 'l6']).
transition(t21, ['l5', 's2'], ['s2', 'l7']).
transition(t22, ['l6', 's2'], ['s2', 'l8']).
transition(t23, ['l7', 's2'], ['s4', 'l33']).
transition(t24, ['l8', 's2'], ['s0', 'l9']).
transition(t25, ['l10', 's2'], ['s2', 'l11']).
transition(t26, ['l11', 's2'], ['s0', 'l12']).
transition(t27, ['l22', 's2'], ['s2', 'l23']).
transition(t28, ['l23', 's2'], ['s0', 'l24']).
transition(t29, ['l25', 's2'], ['s2', 'l26']).
transition(t30, ['l26', 's2'], ['s0', 'l27']).
transition(t31, ['l28', 's2'], ['s2', 'l29']).
transition(t32, ['l28', 's2'], ['s2', 'l30']).
transition(t33, ['l29', 's2'], ['s2', 'l31']).
transition(t34, ['l30', 's2'], ['s4', 'l33']).
transition(t35, ['l31', 's2'], ['s0', 'l32']).
transition(t36, ['l0', 's0'], ['l0', 's1', 'l1']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s4'],1),(['l33'],1)]).
