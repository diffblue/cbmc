extern "C" void __CPROVER_assert(bool, const char *);
struct rec
{
  int x = -1;
};
struct with_braces
{
  int y{7};
};
class holder
{
  rec r;
  with_braces w = {};
  int k;

public:
  explicit holder(int v) : k(v)
  {
  }
  int get() const
  {
    return r.x + w.y + k;
  }
};
int main()
{
  holder h(2);
  __CPROVER_assert(h.get() == 8, "members initialized");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
