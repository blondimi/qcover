place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
place('s6').
place('s7').
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
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['l0', 's2']).
transition(t3, ['l1', 's1'], ['s1', 'l13']).
transition(t4, ['l13', 's1'], ['s3', 'l35']).
transition(t5, ['l22', 's1'], ['s1', 'l28']).
transition(t6, ['l24', 's1'], ['s4', 'l25']).
transition(t7, ['l26', 's1'], ['s1', 'l24']).
transition(t8, ['l28', 's1'], ['s5', 'l25']).
transition(t9, ['l34', 's1'], ['s1', 'l24']).
transition(t10, ['l35', 's1'], ['s1', 'l72']).
transition(t11, ['l69', 's1'], ['s1', 'l73']).
transition(t12, ['l72', 's1'], ['s6', 'l0']).
transition(t13, ['l73', 's1'], ['s7', 'l0']).
transition(t14, ['l75', 's1'], ['s1', 'l71']).
transition(t15, ['l75', 's1'], ['s1', 'l72']).
transition(t16, ['l75', 's1'], ['s1', 'l76']).
transition(t17, ['l76', 's2'], ['s2', 'l78']).
transition(t18, ['l0', 's3'], ['s1', 'l34']).
transition(t19, ['l0', 's4'], ['s1', 'l22']).
transition(t20, ['l0', 's5'], ['s1', 'l26']).
transition(t21, ['l25', 's6'], ['s1', 'l69']).
transition(t22, ['l25', 's7'], ['s1', 'l75']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s2'],1),(['l78'],1)]).
