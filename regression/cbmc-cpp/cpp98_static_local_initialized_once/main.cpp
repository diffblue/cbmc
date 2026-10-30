// N5008 [stmt.dcl]/3: a block-scope variable with static storage duration
// is initialized the first time control passes through its declaration
extern "C" void __CPROVER_assert(bool, const char *);
int constructions = 0;
struct counter
{
  int v;
  counter(int x) : v(x)
  {
    ++constructions;
  }
};
counter &instance()
{
  static counter c(3);
  ++c.v;
  return c;
}
int next_id()
{
  static counter ids = counter(100);
  return ids.v++;
}
int main()
{
  for(int i = 0; i < 3; ++i)
    instance();
  __CPROVER_assert(constructions == 1, "constructed once");
  __CPROVER_assert(instance().v == 7, "state kept between calls");
  int a = next_id();
  int b = next_id();
  __CPROVER_assert(a == 100 && b == 101, "copy-initialized once");
  __CPROVER_assert(constructions == 1, "WRONG (must FAIL)");
}
