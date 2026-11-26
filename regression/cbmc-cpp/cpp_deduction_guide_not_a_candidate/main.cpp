// A class template with a user-defined deduction guide and a partial
// specialization, copy-initialised through an explicit (non-deduced) type.
//
// N5008 [temp.deduct.guide]/1: deduction guides are not found by name lookup
// and are not functions; they are used only when forming class-template-
// argument-deduction candidates ([over.match.class.deduct]), never in ordinary
// overload resolution.  A guide is written like a constructor of the class-
// template name, so `tuple(U...) -> tuple<>` shares the name `tuple`.  When the
// (non-template) copy constructor of `tuple<int, int>` was resolved, the guide
// was wrongly admitted as a function-template candidate and instantiated as an
// ordinary declaration, whose initialiser then resolved the class tag name to a
// type in a value context and tripped an invariant.  The guide must be excluded
// from ordinary overload resolution.

extern "C" int __VERIFIER_nondet_int();
extern "C" void __CPROVER_assert(int, const char *);

template <typename...>
struct tuple;

// User-defined deduction guide sharing the class-template name.
template <typename... U>
tuple(U...) -> tuple<>;

// Partial specialization for exactly two type arguments.
template <typename T1, typename T2>
struct tuple<T1, T2>
{
  T1 a;
  T2 b;
  tuple() = default;
  tuple(T1 x, T2 y) : a(x), b(y)
  {
  }
};

int main()
{
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  tuple<int, int> t(p, q);
  // Copy-initialisation of an explicitly-typed object: the deduction guide
  // must not participate in resolving the copy constructor.
  tuple<int, int> u = t;
  __CPROVER_assert(u.a == p, "copy preserves first member");
  __CPROVER_assert(u.b == q, "copy preserves second member");
  return 0;
}
