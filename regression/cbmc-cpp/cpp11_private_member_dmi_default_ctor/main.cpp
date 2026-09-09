// N5008 [class.default.ctor]/1-4 + [class.access.general]/4: the
// implicitly-declared default constructor is a PUBLIC member, and the
// member initializations it performs are done in the context of the
// class, where private members are accessible.  CBMC judges that access
// from OUTSIDE the class, so a `class` (private by default) holding a
// member whose type has a DEFAULT MEMBER INITIALIZER cannot be
// default-constructed:
//   member 'goto_statet::propagation' is not accessible (private)
//   default constructor of 'struct goto_statet' is not accessible
// Reduced by cvise from 99k preprocessed lines (the dog-food failure of
// src/goto-symex/symex_throw.cpp) to these six declarations; g++ and
// clang++ accept and run it.
extern "C" void __CPROVER_assert(bool, const char *);
struct sharing_mapt
{
  long num = 0;
};
class goto_statet
{
  sharing_mapt propagation;
};
int main()
{
  goto_statet s;
  (void)s;
  __CPROVER_assert(1, "class with private DMI-bearing member default-constructs");
  return 0;
}
