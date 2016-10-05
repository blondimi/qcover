vars
 start x _x ping pong main

rules
start >= 1 ->
   start'=start-1,
    x' = x+1,
    main'=main+1;
start >= 1 ->
   start'=start-1,
   _x' = _x+1,
   main'=main+1;
 
main >= 1, _x >= 1 ->
	main' = main - 1,
	ping' = ping + 1;

 main >= 1, x >= 1 ->
	main' = main - 1,
	_x' = _x + 1,
	x' = x - 1,
	ping' = ping + 1;

ping >= 1, _x >= 1 ->
	ping' = ping -1,
	_x' = _x  - 1,
	x' = x + 1,
	pong' = pong + 1;

pong >= 1, x >= 1 ->
	pong' = pong -1,
	x' = x  - 1,
	_x' = _x + 1,
	ping' = ping + 1;

init
	start=1, x=0, _x=0, ping=0, pong=0, main=0

target
	pong>=1, _x>=1
