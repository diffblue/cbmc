// N5008 [temp.constr.decl]/1 + [temp.constr.atomic]: the constrained
// converting constructor's requires-clause calls a constexpr static
// member function template, `ok<U2>()`, whose body references the
// ENCLOSING CLASS's template parameter.  With U2 deduced as int for the
// argument 0, ok<int>() is false (__is_constructible(nodet*, int); an
// int prvalue is not a null pointer constant, [conv.ptr]/1), so the
// candidate must be removed and pr(const T2&) selected -- for which the
// literal 0 IS a null pointer constant.
//
// KNOWNBUG: the satisfaction check's call-atom constant-fold cannot
// evaluate the CALL (the static member's body needs the class's and
// the member's template maps when type-checked from the satisfaction
// context), leaves the atom "unknown", keeps the unviable candidate,
// and its body fails conversion ("invalid implicit conversion from
// 'signed int' to 'struct nodet *'").  This is the exact shape of
// libstdc++ C++20 pair's `requires(_S_constructible<_U1, _U2>())` --
// the remaining blocker for cpp20_pair_converting_ctor and thereby
// cpp20_map_basic.  The same constraint written INLINE
// (requires(__is_constructible(T2, U2))) works: see the CORE test
// cpp20_requires_class_param_atom.
//
// g++/clang++ verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct nodet
{
  int v;
};

template <class T2>
struct pr
{
  T2 second;
  template <class U2>
  static constexpr bool ok()
  {
    return __is_constructible(T2, U2);
  }
  pr(const T2 &b) : second(b)
  {
  }
  template <class U2 = T2>
    requires(ok<U2>())
  pr(U2 &&b) : second(static_cast<U2 &&>(b))
  {
  }
};

int main()
{
  pr<nodet *> b(0);
  __CPROVER_assert(b.second == nullptr, "null pointer constant selected");
  return 0;
}
