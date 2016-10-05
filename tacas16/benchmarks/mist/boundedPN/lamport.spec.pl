place('p1').
place('p2').
place('p3').
place('x_eq_0').
place('x_eq_1').
place('y_eq_1').
place('q1').
place('q2').
place('q3').
place('q4').
place('q5').
transition(t1, ['p1', 'x_eq_0'], ['p2', 'x_eq_1']).
transition(t2, ['p2', 'x_eq_1'], ['p3', 'x_eq_0']).
transition(t3, ['p3', 'y_eq_1'], ['y_eq_1', 'p1']).
transition(t4, ['x_eq_0', 'q3'], ['x_eq_0', 'q1']).
transition(t5, ['q1'], ['y_eq_1', 'q2']).
transition(t6, ['x_eq_1', 'q2'], ['x_eq_1', 'q5']).
transition(t7, ['x_eq_1', 'q3'], ['x_eq_1', 'q4']).
transition(t8, ['q4'], ['y_eq_1', 'q5']).
transition(t9, ['y_eq_1', 'q5'], ['q3']).
init('p2', 1).
init('x_eq_1', 1).
init('y_eq_1', 1).
init('q5', 1).
target(1, [(['p1'],1),(['q4'],1)]).
