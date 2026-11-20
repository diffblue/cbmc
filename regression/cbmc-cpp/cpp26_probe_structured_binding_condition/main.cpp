// N5008 [stmt.pre], [dcl.struct.bind]: structured binding declaration as a
// condition.
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int a, b;
  explicit operator bool() const
  {
    return a != 0;
  }
};
int main()
{
  int r = 0;
  if(auto [x, y] = P{1, 2})
    r = x + y;
  __CPROVER_assert(r == 3, "structured binding declaration as a condition");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
