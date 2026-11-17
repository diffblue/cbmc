// C++11 thread_local
thread_local int counter = 0;
int main()
{
  counter = 42;
  __CPROVER_assert(counter == 42, "thread_local");
  return 0;
}
