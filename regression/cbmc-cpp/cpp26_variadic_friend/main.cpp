// N5008 [class.friend]: a friend from a pack.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... Ts>
struct S
{
  friend Ts...;

private:
  int v = 5;
};
struct A
{
  int get(S<A, int> &s)
  {
    return s.v;
  }
};
int main()
{
  S<A, int> s;
  __CPROVER_assert(A{}.get(s) == 5, "a friend from a pack");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
