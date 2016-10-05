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
place('l43').
place('l44').
place('l45').
place('l46').
place('l47').
place('l48').
place('l49').
place('l50').
place('l51').
place('l52').
place('l53').
place('l54').
place('l55').
place('l56').
place('l57').
place('l58').
place('l59').
place('l60').
place('l61').
place('l62').
place('l63').
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['l0', 's2']).
transition(t3, ['l1', 's1'], ['s1', 'l9']).
transition(t4, ['l9', 's1'], ['s3', 'l32']).
transition(t5, ['l12', 's1'], ['s4', 'l14']).
transition(t6, ['l15', 's1'], ['s1', 'l24']).
transition(t7, ['l18', 's1'], ['s1', 'l37']).
transition(t8, ['l20', 's1'], ['s5', 'l21']).
transition(t9, ['l22', 's1'], ['s1', 'l12']).
transition(t10, ['l24', 's1'], ['s6', 'l25']).
transition(t11, ['l31', 's1'], ['s1', 'l20']).
transition(t12, ['l32', 's1'], ['s1', 'l58']).
transition(t13, ['l37', 's1'], ['s7', 'l0']).
transition(t14, ['l52', 's1'], ['s8', 'l0']).
transition(t15, ['l52', 's1'], ['s9', 'l0']).
transition(t16, ['l52', 's1'], ['s10', 'l0']).
transition(t17, ['l53', 's1'], ['s1', 'l52']).
transition(t18, ['l55', 's1'], ['s11', 'l39']).
transition(t19, ['l56', 's1'], ['s1', 'l52']).
transition(t20, ['l58', 's1'], ['s12', 'l0']).
transition(t21, ['l59', 's1'], ['s1', 'l55']).
transition(t22, ['l61', 's2'], ['s2', 'l63']).
transition(t23, ['l0', 's3'], ['s1', 'l31']).
transition(t24, ['l0', 's4'], ['s1', 'l13']).
transition(t25, ['l0', 's5'], ['s1', 'l18']).
transition(t26, ['l0', 's6'], ['s1', 'l22']).
transition(t27, ['l39', 's7'], ['s1', 'l15']).
transition(t28, ['l14', 's8'], ['s1', 'l60']).
transition(t29, ['l21', 's9'], ['s1', 'l61']).
transition(t30, ['l25', 's10'], ['s1', 'l56']).
transition(t31, ['l0', 's11'], ['s1', 'l53']).
transition(t32, ['l21', 's12'], ['s1', 'l59']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s2'],1),(['l63'],1)]).
