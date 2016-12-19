#expected result: safe
vars
	begin do sc1 oh_ns point1 oh_a_dt sc2 sc3 point2

rules
begin>=1 ->
	begin'=begin-1,
	do'=do+1;

do>=1 ->
	do'=do-1,
	sc1'=sc1+1;

sc1>=1 ->
	sc1'=sc1-1,
	oh_ns'=oh_ns+1;

oh_ns>=1 ->
	oh_ns'=oh_ns-1,
	point1'=point1+1;

oh_ns>=1 ->
	oh_ns'=oh_ns-1,
	point2'=point2+1;

point1>=1 ->
	point1'=point1-1,
	oh_a_dt'=oh_a_dt+1;

oh_a_dt>=1 ->
	oh_a_dt'=oh_a_dt-1,
	point2'=point2+1;

oh_a_dt>=1 ->
	oh_a_dt'=oh_a_dt-1,
	sc2'=sc2+1;

oh_a_dt>=1 ->
	oh_a_dt'=oh_a_dt-1,
	sc3'=sc3+1;

sc2>=1 ->
	sc2'=sc2-1,
	point2'=point2+1 ;

sc3>=1 ->
	sc3'=sc3-1,
	point2'=point2+1 ;

point2>=1 ->
	point2'=point2-1,
	do'=do+1;

init
	begin=1, do=0, sc1=0, oh_ns=0, point1=0, oh_a_dt=0, sc2=0, sc3=0, point2=0

target
	point1>=1, point2>=1

invariants
begin=1, do=1, sc1=1, oh_ns=1, point1=1, oh_a_dt=1, sc2=1, sc3=1, point2=1
