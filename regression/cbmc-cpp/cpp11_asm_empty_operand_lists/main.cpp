extern "C" void __CPROVER_assert(bool, const char *);
template <typename T>
inline T dontcare()
{
  T t;
  asm("" : "=r"(t)::);
  return t;
}
int main()
{
  int a = 1, b;
  asm volatile("" : "=r"(b) : "r"(a) : "memory");
  asm("" : : : "memory");
  asm("" ::: "memory");
  asm("" : "=r"(b)::"memory");
  asm("nop" ::);
  int x = dontcare<int>();
  int reached = 1;
  __CPROVER_assert(reached == 1, "statements after the asm forms are reached");
  return x == x ? 0 : 1;
}
