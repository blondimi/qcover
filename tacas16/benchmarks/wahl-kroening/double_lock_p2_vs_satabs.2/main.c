int count;

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

int mutexa,mutexb;
void my_thread1()
{
  acquire(mutexa);
  count++;
  count--;
  release(mutexa);
}

void my_thread2()
{
  acquire(mutexb);
  count--;
  count++;
  release(mutexb);
}

void monitor()
{
  while(1)
  {

    acquire(mutexa);
    __CPROVER_assert(count >= -1,"p1");
    release(mutexa);

    acquire(mutexb);
    __CPROVER_assert(count <= 1,"p2");
    release(mutexb);

  }
}

int main(void)
{
  __CPROVER_ASYNC_01: monitor();
  while(1)
  {
      __CPROVER_ASYNC_02: my_thread1();
      __CPROVER_ASYNC_03: my_thread2();
  }
}

