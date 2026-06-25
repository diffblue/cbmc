// A class that has a (converting) constructor template but is not itself a
// class template.  Copying an object of such a class must select the
// (implicitly declared) copy constructor, not a by-value specialisation of the
// constructor template.  N5008 [class.copy.ctor]/2: a constructor whose first
// parameter is its own class type by value is ill-formed, so the deduced
// specialisation `M(M)` (with the template parameter deduced as M) is not a
// usable candidate.  Were it selected, materialising its by-value parameter
// would recursively construct another M without bound
// (cf. [over.best.ics]/4 Note 2).

extern "C" unsigned long __VERIFIER_nondet_ulong();
extern "C" void __CPROVER_assert(int, const char *);

struct M
{
  unsigned long v;
  M() = default;
  // Converting constructor template.
  template <typename T>
  M(T i) : v(i)
  {
  }
};

int main()
{
  unsigned long x = __VERIFIER_nondet_ulong();

  // Direct-initialisation through the constructor template, T deduced as
  // 'unsigned long' (a perfect match) rather than as M.
  M a{x};
  __CPROVER_assert(a.v == x, "template constructor stores the argument");

  // Copy-initialisation: must use the copy constructor (binds by reference),
  // preserving the value, rather than the bodyless by-value M(M) instance.
  M b = a;
  __CPROVER_assert(b.v == x, "copy constructor preserves the value");

  // Copy again from a distinct lvalue to exercise the copy path once more.
  M c = b;
  __CPROVER_assert(c.v == x, "second copy preserves the value");

  return 0;
}
