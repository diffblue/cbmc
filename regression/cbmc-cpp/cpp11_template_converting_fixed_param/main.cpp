// N5008 [over.match.funcs], [over.ics.user]: a function template with a
// non-deduced (fixed) parameter of class type S is viable for an argument that
// is convertible to S through a user-defined conversion (here const char* -> S
// via the converting constructor S(const char*)).  This is the shape of
// util/invariant.h's report_invariant_failure(const std::string&, ...) called
// with __FILE__ (a const char*).  CBMC wrongly dropped such a template from the
// overload set ("found no match"); g++/clang accept it.

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int v;
  S(const char *) : v(7) {}
};

template <typename U = int>
int g(S x)
{
  return x.v;
}

int main()
{
  __CPROVER_assert(g("f") == 7, "converting fixed param, template viable");
  __CPROVER_assert(g("f") != 7, "WRONG must FAIL");
  return 0;
}
