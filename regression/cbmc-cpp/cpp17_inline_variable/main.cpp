// C++17 inline variable
struct S
{
  static inline int x = 42;
};
int main()
{
  __CPROVER_assert(S::x == 42, "inline var");
  return 0;
}
