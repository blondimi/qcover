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
transition(t1, ['l0', 's0'], ['s0', 'l2']).
transition(t2, ['l0', 's0'], ['s0', 'l3']).
transition(t3, ['l1', 's0'], ['s0', 'l2']).
transition(t4, ['l1', 's0'], ['s0', 'l3']).
transition(t5, ['l2', 's0'], ['s0', 'l4']).
transition(t6, ['l2', 's0'], ['s0', 'l5']).
transition(t7, ['l3', 's0'], ['s0', 'l4']).
transition(t8, ['l3', 's0'], ['s0', 'l5']).
transition(t9, ['l4', 's0'], ['s0', 'l6']).
transition(t10, ['l5', 's0'], ['s0', 'l7']).
transition(t11, ['l6', 's0'], ['s0', 'l8']).
transition(t12, ['l7', 's0'], ['s0', 'l9']).
transition(t13, ['l8', 's0'], ['s0', 'l10']).
transition(t14, ['l8', 's0'], ['s0', 'l11']).
transition(t15, ['l9', 's0'], ['s0', 'l10']).
transition(t16, ['l9', 's0'], ['s0', 'l11']).
transition(t17, ['l10', 's0'], ['s0', 'l12']).
transition(t18, ['l11', 's0'], ['s0', 'l13']).
transition(t19, ['l12', 's0'], ['s0', 'l14']).
transition(t20, ['l13', 's0'], ['s0', 'l15']).
transition(t21, ['l14', 's0'], ['s4', 'l20']).
transition(t22, ['l15', 's0'], ['s0', 'l17']).
transition(t23, ['l16', 's0'], ['l16', 's0']).
transition(t24, ['l17', 's0'], ['l17', 's0']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s4'],1),(['l20'],1)]).
