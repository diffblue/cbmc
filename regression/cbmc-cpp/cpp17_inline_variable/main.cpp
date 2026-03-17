// C++17 inline variables
struct S
{
  static inline int x = 42;
};
int main()
{
  __CPROVER_assert(S::x == 42, "inline variable");
  return 0;
}
