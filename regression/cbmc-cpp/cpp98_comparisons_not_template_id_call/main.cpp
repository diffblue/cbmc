extern "C" void __CPROVER_assert(bool, const char *);

// [temp.names]/3: `<' after a name starts a template-argument-list only if
// the name is a template-name; `a<b>(c)' with a variable a is
// `(a < b) > (c)'
int limit = 2;

struct base
{
  template <int N>
  int add(int x)
  {
    return x + N;
  }
};

struct derived : base
{
  int value()
  {
    // a member template of the base: still a call
    return add<2>(3);
  }
};

int main()
{
  int a = 1, b = 2, c = 0, d = 5;
  bool r1 = a<limit>(0);
  bool r2 = a<b + 1>(c);
  bool r3 = (b<a>(c, d));
  __CPROVER_assert(r1 && r2 && !r3, "comparisons");

  derived x;
  __CPROVER_assert(x.value() == 5, "template-id");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
