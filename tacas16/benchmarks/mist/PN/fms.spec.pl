place('x1').
place('x2').
place('x3').
place('x4').
place('x5').
place('x6').
place('x7').
place('x8').
place('x9').
place('x10').
place('x11').
place('x12').
place('x13').
place('x14').
place('x15').
place('x16').
place('x17').
place('x18').
place('x19').
place('x20').
place('x21').
place('x22').
transition(t1, ['x1'], ['x5']).
transition(t2, ['x2', 'x12'], ['x6']).
transition(t3, ['x3'], ['x7']).
transition(t4, ['x4'], ['x8']).
transition(t5, ['x5', 'x9'], ['x10']).
transition(t6, ['x16'], ['x2']).
transition(t7, ['x6'], ['x11']).
transition(t8, ['x7', 'x14'], ['x13']).
transition(t9, ['x8', 'x14'], ['x14', 'x15']).
transition(t10, ['x10'], ['x9', 'x16']).
transition(t11, ['x11', 'x17'], ['x18']).
transition(t12, ['x19'], ['x12']).
transition(t13, ['x13'], ['x14', 'x19']).
transition(t14, ['x15'], ['x4']).
transition(t15, ['x16'], ['x20']).
transition(t16, ['x18'], ['x17', 'x21']).
transition(t17, ['x19'], ['x22']).
transition(t18, ['x20'], ['x1']).
transition(t19, ['x21'], ['x1', 'x3']).
transition(t20, ['x22'], ['x3']).
init('x1', 1).
transition(init1, [], ['x1']).
init('x3', 1).
transition(init2, [], ['x3']).
init('x4', 1).
transition(init3, [], ['x4']).
init('x9', 3).
init('x14', 1).
init('x17', 2).
target(1, [(['x13'],2)]).
