// N5008 [temp.variadic]/5: a pack expansion `A...` of a class template
// parameter pack that appears in the type of a data member -- here the
// parameter list of a member function-pointer type `int (*)(A...)` -- must
// expand to one element per pack member when the class template is
// instantiated.
//
// This is the analogue of cpp11_variadic_pack_in_member_funptr_type for a
// *primary* variadic class template `S<A...>` (rather than a partial
// specialization `Func<R(A...)>`).  The two follow different instantiation
// paths: the partial-specialization path runs template_mapt::apply over the
// member types (which expands the function-pointer pointee), whereas the
// primary-template path type-checks the member declarator directly.  The latter
// previously substituted the pointee pack as a single (scalar) element,
// collapsing `int (*)(A...)` for S<int,int> to `int (*)(<first>)`, so that
// `s.fp = add` no longer bound `add` (it decayed to a null pointer) and the
// program verified only VACUOUSLY.
//
// Header-free and non-vacuous (assertion 2 must FAIL).

extern "C" void __CPROVER_assert(int, const char *);

template <class... A>
struct S
{
  int (*fp)(A...) = nullptr; // pack expansion inside a data-member type
};

int add(int a, int b)
{
  return a + b;
}

int main()
{
  S<int, int> s;
  s.fp = add; // binds only if fp is int(*)(int,int), not the collapsed int(*)(int)
  int r = s.fp(2, 3);
  __CPROVER_assert(r == 5, "primary variadic class member funptr full arity");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
