place('beg0').
place('at20').
place('testturn0').
place('at30').
place('cs0').
place('beg1').
place('at21').
place('testturn1').
place('at31').
place('cs1').
place('c0eq1').
place('c0eq0').
place('c1eq1').
place('c1eq0').
place('turneq0').
place('turneq1').
transition(t1, ['beg0', 'c0eq1'], ['c0eq0', 'at20']).
transition(t2, ['beg1', 'c1eq1'], ['c1eq0', 'at21']).
transition(t3, ['at20', 'c1eq0'], ['c1eq0', 'testturn0']).
transition(t4, ['at21', 'c0eq0'], ['c0eq0', 'testturn1']).
transition(t5, ['testturn0', 'turneq0'], ['turneq0', 'at20']).
transition(t6, ['testturn1', 'turneq1'], ['turneq1', 'at21']).
transition(t7, ['testturn0', 'c0eq0', 'turneq1'], ['turneq1', 'c0eq1', 'at30']).
transition(t8, ['testturn1', 'c1eq0', 'turneq0'], ['turneq0', 'c1eq1', 'at31']).
transition(t9, ['at30', 'turneq0'], ['turneq0', 'beg0']).
transition(t10, ['at31', 'turneq1'], ['turneq1', 'beg1']).
transition(t11, ['at20', 'c1eq1'], ['c1eq1', 'cs0']).
transition(t12, ['at21', 'c0eq1'], ['c0eq1', 'cs1']).
transition(t13, ['cs0', 'c0eq0', 'turneq0'], ['beg0', 'c0eq1', 'turneq1']).
transition(t14, ['cs1', 'c1eq0', 'turneq1'], ['beg1', 'c1eq1', 'turneq0']).
init('beg0', 1).
init('beg1', 1).
init('turneq0', 1).
init('c0eq1', 1).
init('c1eq1', 1).
target(1, [(['cs0'],1),(['cs1'],1)]).
