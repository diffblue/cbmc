extern "C" void __CPROVER_assert(bool, const char *);
int calls;
int next()
{
  return ++calls;
}
// N5008 [stmt.dcl]/3: a block-scope variable with static storage duration
// that is not constant-initialized is initialized the first time control
// passes through its declaration, from that call's parameters
int first_argument(int a)
{
  static int first = a + next();
  return first;
}
struct translator
{
  int offset;
  int translate(int c) const
  {
    return c + offset;
  }
};
struct matcher
{
  translator tr;
  bool operator()(int c) const
  {
    // libstdc++'s _AnyMatcher::operator(): the initializer uses `this'
    static auto nul = tr.translate(0);
    return tr.translate(c) != nul;
  }
};
int main()
{
  int x = first_argument(10);
  int y = first_argument(20);
  __CPROVER_assert(x == 11 && y == 11 && calls == 1, "initialized once");
  matcher m{{5}};
  __CPROVER_assert(m(1), "initializer uses this");
  __CPROVER_assert(y == 21, "WRONG (must FAIL)");
  return 0;
}
