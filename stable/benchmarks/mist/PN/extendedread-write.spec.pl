place('x0').
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
place('x23').
transition(t1, ['x1'], ['x0']).
transition(t2, ['x0', 'x11'], ['x1', 'x10']).
transition(t3, ['x1', 'x7', 'x9', ('x10', 45)], ['x7', ('x10', 45), 'x2', 'x3']).
transition(t4, ['x2', 'x4', 'x6'], ['x1', 'x9']).
transition(t5, [('x5', 5)], [('x6', 5)]).
transition(t6, ['x3'], ['x4', 'x5']).
transition(t7, ['x8', ('x10', 45), ('x12', 90)], [('x12', 90), 'x7']).
transition(t8, ['x7', ('x13', 42)], [('x13', 42), 'x8', ('x10', 45)]).
transition(t9, ['x9', 'x10', 'x13', 'x15'], ['x9', 'x11', 'x12', 'x16']).
transition(t10, ['x9', 'x10', 'x13', 'x14'], ['x9', 'x11', 'x12', 'x16']).
transition(t11, ['x7', 'x9', ('x12', 49), 'x21'], ['x7', 'x9', ('x12', 45), ('x13', 4), 'x20']).
transition(t12, ['x8', 'x9', ('x12', 4), 'x21'], ['x8', 'x9', ('x13', 4), 'x20']).
transition(t13, ['x13', 'x15'], ['x12', 'x16']).
transition(t14, [('x16', 4), 'x17'], ['x19']).
transition(t15, [('x16', 2), 'x18'], ['x19']).
transition(t16, [('x12', 45), 'x20'], [('x12', 45), 'x14', ('x15', 3), 'x17']).
transition(t17, [('x13', 46), 'x20'], [('x13', 44), ('x12', 2), 'x14', 'x15', 'x18']).
transition(t18, ['x19'], ['x21']).
transition(t19, ['x22', 'x23'], ['x21']).
transition(t20, ['x21'], ['x22', 'x23']).
transition(t21, [], ['x22']).
transition(t22, ['x21'], ['x23']).
init('x2', 1).
init('x4', 1).
init('x6', 5).
init('x7', 1).
init('x10', 45).
init('x12', 90).
init('x23', 1).
transition(init1, [], ['x23']).
target(1, [(['x2'],1),(['x11'],1)]).
