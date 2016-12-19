//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables
#define assume(e) __CPROVER_assume(e)

#define acquire(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==0); \
	m = 1; \
	__CPROVER_atomic_end(); \
}
#define release(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==1); \
	m = 0; \
	__CPROVER_atomic_end(); \
}

int m = 0;
inline int calculateNext(int s2){ 
	int cnex;
	do cnex = rand();
	while(cnex == s2 || cnex == 0);
	return cnex;
}

volatile int seed; 

#define NUM 10

inline int PseudoRandomUsingAtomic_nextInt() {
	int read, nexts, nextInt_return;

	assert(seed != 0);

	acquire(m);
	read = seed;
	nexts = calculateNext(read);
	//assert(nexts != read); 
	seed = nexts;
	release(m);
	nextInt_return = nexts % NUM;
	return nextInt_return;
}

int main()
{
	seed = 1;
	while(1) { __CPROVER_ASYNC_01: (PseudoRandomUsingAtomic_nextInt()); }
}
