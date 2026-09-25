// N5008 [temp.variadic]/5: a class-template parameter pack used as a
// constructor parameter pack of length N is instantiated as N constructor
// parameters, and a pack expansion `a...` in the constructor body is replaced
// by the N corresponding arguments.  Here N == 3, exercised in two distinct
// expansion contexts: a brace-enclosed initializer list (`int t[]={a...}`) and
// a function-call argument list (`s.set(a...)`).
//
// Header-free and non-vacuous: the operands are nondet and assertion 4 is a
// deliberately wrong claim that must FAIL, so a vacuous (truncated) proof
// cannot pass.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

struct Sink
{
  int a, b, c;
  void set(int x, int y, int z)
  {
    a = x;
    b = y;
    c = z;
  }
};

template <class... A>
struct Holder
{
  int p, q, r;
  Sink s;
  Holder(A... a)
  {
    int t[] = {a...};
    p = t[0];
    q = t[1];
    r = t[2];
    s.set(a...);
  }
};

int main()
{
  int x = nondet_int();
  int y = nondet_int();
  int z = nondet_int();
  Holder<int, int, int> h(x, y, z);
  __CPROVER_assert(h.p == x, "brace-init element 0");
  __CPROVER_assert(h.r == z, "brace-init element 2");
  __CPROVER_assert(h.s.b == y, "call-arg element 1");
  __CPROVER_assert(h.r == x, "WRONG must FAIL");
  return 0;
}
