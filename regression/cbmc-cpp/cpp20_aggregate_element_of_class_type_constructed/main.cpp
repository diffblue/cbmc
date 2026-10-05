// N5008 [dcl.init.aggr]/4.2: each element of an aggregate is
// copy-initialized from its initializer; an element of class type is
// constructed, not assigned to
extern "C" void __CPROVER_assert(bool, const char *);
struct conv {
  int v;
  conv(int x) : v(2 * x) {}
  conv &operator=(const conv &) = delete;
};
struct agg {
  conv c;
  int k;
};
template <class H> struct leaf {
  H value;
};
int main() {
  agg a(3, 4);
  __CPROVER_assert(a.c.v == 6 && a.k == 4, "parenthesized");
  leaf<conv> l(5);
  __CPROVER_assert(l.value.v == 10, "one element");
  agg b{7, 1};
  __CPROVER_assert(b.c.v == 14, "braced");
  __CPROVER_assert(a.c.v == 3, "WRONG (must FAIL)");
}
