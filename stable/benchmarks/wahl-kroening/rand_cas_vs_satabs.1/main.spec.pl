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
place('l34').
place('l35').
place('l36').
place('l37').
place('l38').
place('l39').
place('l40').
place('l41').
place('l42').
transition(t1, ['l0', 's0'], ['s0', 'l2']).
transition(t2, ['l0', 's0'], ['s0', 'l3']).
transition(t3, ['l1', 's0'], ['s0', 'l2']).
transition(t4, ['l1', 's0'], ['s0', 'l3']).
transition(t5, ['l2', 's0'], ['s0', 'l4']).
transition(t6, ['l3', 's0'], ['s0', 'l5']).
transition(t7, ['l6', 's0'], ['s0', 'l8']).
transition(t8, ['l6', 's0'], ['s0', 'l9']).
transition(t9, ['l7', 's0'], ['s0', 'l8']).
transition(t10, ['l7', 's0'], ['s0', 'l9']).
transition(t11, ['l8', 's0'], ['s0', 'l10']).
transition(t12, ['l9', 's0'], ['s0', 'l11']).
transition(t13, ['l10', 's0'], ['s0', 'l12']).
transition(t14, ['l11', 's0'], ['s0', 'l13']).
transition(t15, ['l12', 's0'], ['s0', 'l10']).
transition(t16, ['l12', 's0'], ['s0', 'l14']).
transition(t17, ['l13', 's0'], ['s0', 'l11']).
transition(t18, ['l13', 's0'], ['s0', 'l15']).
transition(t19, ['l14', 's0'], ['s2', 'l16']).
transition(t20, ['l15', 's0'], ['s2', 'l17']).
transition(t21, ['l24', 's0'], ['s0', 'l26']).
transition(t22, ['l24', 's0'], ['s0', 'l28']).
transition(t23, ['l25', 's0'], ['s0', 'l27']).
transition(t24, ['l25', 's0'], ['s0', 'l29']).
transition(t25, ['l26', 's0'], ['s0', 'l30']).
transition(t26, ['l27', 's0'], ['s0', 'l31']).
transition(t27, ['l28', 's0'], ['s0', 'l8']).
transition(t28, ['l29', 's0'], ['s0', 'l9']).
transition(t29, ['l30', 's0'], ['s0', 'l32']).
transition(t30, ['l30', 's0'], ['s0', 'l33']).
transition(t31, ['l31', 's0'], ['s0', 'l32']).
transition(t32, ['l31', 's0'], ['s0', 'l33']).
transition(t33, ['l32', 's0'], ['s4', 'l42']).
transition(t34, ['l33', 's0'], ['s0', 'l35']).
transition(t35, ['l36', 's0'], ['s0', 'l2']).
transition(t36, ['l37', 's0'], ['s0', 'l3']).
transition(t37, ['l38', 's0'], ['s0', 'l40']).
transition(t38, ['l39', 's0'], ['s0', 'l41']).
transition(t39, ['l4', 's1'], ['s0', 'l36']).
transition(t40, ['l5', 's1'], ['s0', 'l37']).
transition(t41, ['l16', 's2'], ['s2', 'l18']).
transition(t42, ['l16', 's2'], ['s2', 'l20']).
transition(t43, ['l17', 's2'], ['s2', 'l19']).
transition(t44, ['l17', 's2'], ['s2', 'l21']).
transition(t45, ['l18', 's2'], ['s2', 'l22']).
transition(t46, ['l19', 's2'], ['s2', 'l23']).
transition(t47, ['l20', 's2'], ['s2', 'l22']).
transition(t48, ['l21', 's2'], ['s2', 'l23']).
transition(t49, ['l22', 's2'], ['s0', 'l24']).
transition(t50, ['l23', 's2'], ['s0', 'l25']).
transition(t51, ['l4', 's0'], ['l4', 's1', 'l6']).
transition(t52, ['l5', 's0'], ['l5', 's1', 'l7']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s4'],1),(['l42'],1)]).
