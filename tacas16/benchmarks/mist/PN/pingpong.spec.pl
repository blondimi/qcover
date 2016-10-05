place('start').
place('x').
place('_x').
place('ping').
place('pong').
place('main').
transition(t1, ['start'], ['x', 'main']).
transition(t2, ['start'], ['_x', 'main']).
transition(t3, ['main', '_x'], ['_x', 'ping']).
transition(t4, ['main', 'x'], ['_x', 'ping']).
transition(t5, ['ping', '_x'], ['x', 'pong']).
transition(t6, ['pong', 'x'], ['_x', 'ping']).
init('start', 1).
target(1, [(['pong'],1),(['_x'],1)]).
