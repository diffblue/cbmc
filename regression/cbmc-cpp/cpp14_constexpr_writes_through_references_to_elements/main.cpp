// N5008 [expr.const]/5: a constant expression may modify an object whose
// lifetime began within its evaluation, also through a reference or pointer
// bound to one of its subobjects.  [stmt.ranged]/1: `for(auto &e : a)'
// binds e to each element of a in turn.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int d[4];
};

constexpr int local_array()
{
  int d[4] = {};
  for(auto &e : d)
    e = 3;
  return d[2];
}

constexpr int member_array()
{
  S s{};
  for(auto &e : s.d)
    e = 5;
  int total = 0;
  for(const auto &e : s.d)
    total += e;
  return total;
}

constexpr int through_a_pointer()
{
  S s{};
  int *p = &s.d[1];
  *p = 7;
  ++*p;
  return s.d[1];
}

constexpr int a = local_array();
constexpr int b = member_array();
constexpr int c = through_a_pointer();

int main()
{
  __CPROVER_assert(a == 3, "local array");
  __CPROVER_assert(b == 20, "member array");
  __CPROVER_assert(c == 8, "through a pointer");
  __CPROVER_assert(a == 4, "WRONG (must FAIL)");
  return 0;
}
