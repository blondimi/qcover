//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only

#define WORDT_NULL 0
typedef int WORDT;
typedef int SIZET;
typedef int WORDT_Ptr;
typedef int WORDT_Ptr_Ptr;
typedef int E;

#define MEMSIZE (2*32+1) //0 for "NULL"
WORDT memory[MEMSIZE];
#define INDIR(cell,idx) memory[cell+idx]

SIZET next_alloc_idx = 1;

volatile WORDT_Ptr top;

#define index_malloc(curr_alloc_idx){\
	__CPROVER_atomic_begin();\
	if(next_alloc_idx+2-1 > MEMSIZE) curr_alloc_idx = WORDT_NULL;\
	else curr_alloc_idx = next_alloc_idx, next_alloc_idx += 2;\
	__CPROVER_atomic_end();\
}

#define isEmpty() (top == WORDT_NULL)

#define exit(r) __CPROVER_assume(0);

void push(E d) {
	WORDT_Ptr oldTop, newTop;
	index_malloc(newTop);
	if(newTop == WORDT_NULL)
		exit(-1);
	INDIR(newTop,0) = d;
	while (1) {
		oldTop = top;
		INDIR(newTop,1) = oldTop;
		__CPROVER_atomic_begin();
		int ret;
		if (top == oldTop) {
			top = newTop; 
			ret = 1;
		}else ret = 0;
		__CPROVER_atomic_end();
		if(ret)	return;
	}
}

int main()
{
	top = WORDT_NULL;
	while(1) { __CPROVER_ASYNC_01: while(1) push(10), assert(!isEmpty()); }
}

