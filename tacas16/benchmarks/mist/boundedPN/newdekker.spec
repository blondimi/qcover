#expected result: safe
#Dekker mutual exclusion protocol

vars
	beg0 at20 testturn0 at30 cs0 beg1 at21 testturn1 at31 cs1 c0eq1 c0eq0 c1eq1 c1eq0 turneq0 turneq1

rules

beg0>=1, c0eq1>=1 ->
	beg0'=beg0-1,
	c0eq1'=c0eq1-1,
	c0eq0'=c0eq0+1,
	at20'=at20+1;

beg1>=1, c1eq1>=1 ->
	beg1'=beg1-1,
	c1eq1'=c1eq1-1,
	c1eq0'=c1eq0+1,
	at21'=at21+1;

at20>=1, c1eq0>=1 ->
	at20'=at20-1,
	testturn0'=testturn0+1;

at21>=1, c0eq0>=1 ->
	at21'=at21-1,
	testturn1'=testturn1+1;

testturn0>=1, turneq0>=1 ->
	testturn0'=testturn0-1,
	at20'=at20+1;

testturn1>=1, turneq1>=1 ->
	testturn1'=testturn1-1,
	at21'=at21+1;

testturn0>=1, c0eq0>=1, turneq1>=1 ->
	c0eq0'=c0eq0-1,
	c0eq1'=c0eq1+1,
	testturn0'=testturn0-1,
	at30'=at30+1;

testturn1>=1, c1eq0>=1, turneq0>=1 ->
	c1eq0'=c1eq0-1,
	c1eq1'=c1eq1+1,
	testturn1'=testturn1-1,
	at31'=at31+1;

at30>=1, turneq0>=1 ->
	at30'=at30-1,
	beg0'=beg0+1;

at31>=1, turneq1>=1 ->
	at31'=at31-1,
	beg1'=beg1+1;

at20>=1, c1eq1>=1 ->
	at20'=at20-1,
	cs0'=cs0+1;

at21>=1, c0eq1>=1 ->
	at21'=at21-1,
	cs1'=cs1+1;

cs0>=1, c0eq0>=1, turneq0>=1 ->
	cs0'=cs0-1,
	beg0'=beg0+1,
	c0eq0'=c0eq0-1,
	c0eq1'=c0eq1+1,
	turneq0'=turneq0-1,
	turneq1'=turneq1+1;

cs1>=1, c1eq0>=1, turneq1>=1 ->
	cs1'=cs1-1,
	beg1'=beg1+1,
	c1eq0'=c1eq0-1,
	c1eq1'=c1eq1+1,
	turneq1'=turneq1-1,
	turneq0'=turneq0+1;

init
	beg0=1, beg1=1, turneq0=1, turneq1=0, c0eq0=0, c0eq1=1, c1eq0=0, c1eq1=1, at20=0, at21=0,
	testturn0=0, testturn1=0, at30=0, at31=0, cs0=0, cs1=0
target
	cs0>=1, cs1>=1

invariants
c0eq0=1, c0eq1=1
c1eq0=1, c1eq1=1
turneq0=1, turneq1=1
beg0=1, at20=1, testturn0=1, at30=1, cs0=1
beg1=1, at21=1, testturn1=1, at31=1, cs1=1


