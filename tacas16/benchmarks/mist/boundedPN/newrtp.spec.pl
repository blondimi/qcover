place('begin').
place('do').
place('sc1').
place('oh_ns').
place('point1').
place('oh_a_dt').
place('sc2').
place('sc3').
place('point2').
transition(t1, ['begin'], ['do']).
transition(t2, ['do'], ['sc1']).
transition(t3, ['sc1'], ['oh_ns']).
transition(t4, ['oh_ns'], ['point1']).
transition(t5, ['oh_ns'], ['point2']).
transition(t6, ['point1'], ['oh_a_dt']).
transition(t7, ['oh_a_dt'], ['point2']).
transition(t8, ['oh_a_dt'], ['sc2']).
transition(t9, ['oh_a_dt'], ['sc3']).
transition(t10, ['sc2'], ['point2']).
transition(t11, ['sc3'], ['point2']).
transition(t12, ['point2'], ['do']).
init('begin', 1).
target(1, [(['point1'],1),(['point2'],1)]).
