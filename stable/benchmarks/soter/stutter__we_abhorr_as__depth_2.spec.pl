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
place('l64').
place('l65').
place('l66').
place('l67').
place('l68').
place('l69').
place('l70').
place('l71').
place('l72').
place('l73').
place('l74').
place('l75').
place('l76').
place('l77').
place('l78').
place('l79').
place('l80').
place('l81').
place('l82').
place('l83').
place('l84').
place('l85').
place('l86').
place('l87').
place('l88').
place('l89').
place('l90').
place('l91').
place('l92').
place('l93').
place('l94').
place('l95').
place('l96').
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['l0', 's2']).
transition(t3, ['l1', 's1'], ['s1', 'l13']).
transition(t4, ['l13', 's1'], ['s3', 'l36']).
transition(t5, ['l22', 's1'], ['s1', 'l28']).
transition(t6, ['l24', 's1'], ['s4', 'l25']).
transition(t7, ['l26', 's1'], ['s1', 'l24']).
transition(t8, ['l28', 's1'], ['s5', 'l29']).
transition(t9, ['l35', 's1'], ['s1', 'l24']).
transition(t10, ['l36', 's1'], ['s1', 'l89']).
transition(t11, ['l83', 's1'], ['s1', 'l90']).
transition(t12, ['l84', 's1'], ['s1', 'l90']).
transition(t13, ['l89', 's1'], ['s6', 'l0']).
transition(t14, ['l89', 's1'], ['s7', 'l0']).
transition(t15, ['l90', 's1'], ['s8', 'l0']).
transition(t16, ['l90', 's1'], ['s9', 'l0']).
transition(t17, ['l92', 's1'], ['s1', 'l86']).
transition(t18, ['l92', 's1'], ['s1', 'l94']).
transition(t19, ['l93', 's1'], ['s1', 'l88']).
transition(t20, ['l93', 's1'], ['s1', 'l89']).
transition(t21, ['l94', 's2'], ['s2', 'l96']).
transition(t22, ['l0', 's3'], ['s1', 'l35']).
transition(t23, ['l0', 's4'], ['s1', 'l22']).
transition(t24, ['l0', 's5'], ['s1', 'l26']).
transition(t25, ['l25', 's6'], ['s1', 'l83']).
transition(t26, ['l29', 's7'], ['s1', 'l84']).
transition(t27, ['l25', 's8'], ['s1', 'l92']).
transition(t28, ['l29', 's9'], ['s1', 'l93']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s2'],1),(['l96'],1)]).
