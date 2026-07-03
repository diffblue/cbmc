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
// CBMC elaborates `S<char>` eagerly at the early reference (from the not-yet-
// defined primary template), producing a spurious empty-but-complete class and
// dropping the instance's link back to the template; the later definition's
// members are then permanently masked, so `g_in.read()` fails with
// "symbol 'read' is unknown".  This is the reduced form (cvise, from a
// preprocessed <istream> translation unit) of the dog-food failures in
// lispexpr.cpp and parser.cpp, where <iosfwd> forward-declares
// std::basic_istream before <istream> defines it.
//
// KNOWN BUG.  A fix must defer the instantiation until the template is defined,
// but the obvious guards are unsafe: keying off the primary template's class
// body mis-fires for partial-specialization-defined templates such as
// std::function (whose primary is bodyless), and simply leaving the instance
// incomplete breaks later layout computation for library types (e.g. the
// std::ostringstream bit-field padding invariant in <iostream>).  A correct fix
// needs reliable "definition seen" tracking.  Flip to CORE once fixed;
// assertion.2 must then FAIL (non-vacuity).

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
