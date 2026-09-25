// N5008 [temp.inst]/1 with [temp.point]: a class template specialization is
// implicitly instantiated -- and thus completed -- only from a *definition* of
// the template, at a point where its completeness is required.  Referencing a
// specialization while the template is merely forward-declared (e.g. as a
// by-value function parameter in a *declaration*, which does not require a
// complete type) must not fix the specialization's members prematurely.
//
// Here `S<char>` is referenced by `other`'s parameter while `S` is only
// forward-declared, then `S` is defined with a `read()` member.  The call
// `g_in.read()` must resolve to that member.  g++ and clang++ accept this.
//
// CBMC used to elaborate `S<char>` eagerly at the early reference (from the
// not-yet-defined primary template), producing a spurious empty-but-complete
// class and dropping the instance's link back to the template; the later
// definition's members were then permanently masked, so `g_in.read()` failed
// with "symbol 'read' is unknown".  This is the reduced form (cvise, from a
// preprocessed <istream> translation unit) of the dog-food failures in
// lispexpr.cpp and parser.cpp, where <iosfwd> forward-declares
// std::basic_istream before <istream> defines it.
//
// Fixed by definition-seen tracking: typecheck_class_template records
// ID_C_template_defined on a class-template declaration once a class body has
// been seen for it, and elaborate_class_template defers instantiation of a
// specialization whose selected template is not yet defined, so it is
// elaborated correctly once the definition is available.  assertion.2 provides
// non-vacuity (it must FAIL).

extern "C" void __CPROVER_assert(int, const char *);

template <typename>
struct S;

void other(S<char>); // references S<char> while S is only forward-declared

template <typename>
struct S
{
  int read()
  {
    return 7;
  }
};

S<char> g_in;

int main()
{
  __CPROVER_assert(g_in.read() == 7, "member from later definition resolves");
  __CPROVER_assert(g_in.read() != 7, "WRONG must FAIL");
  return 0;
}
