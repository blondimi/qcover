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

  acquire(mutexa);
  count--;
  count++;
  release(mutexa);

}

void monitor()
{
  while(1)
  {
    acquire(mutexa);
    __CPROVER_assert(count >= -1,"p1");
    release(mutexa);
  }
}

int main(void)
{
  __CPROVER_ASYNC_01: monitor();
  while(1)
  {
      __CPROVER_ASYNC_02: my_thread1();
  }
}

