// Per [basic.scope.temp] and [temp.variadic]/5: a template parameter
// pack's short name used inside a template refers to THAT template's
// pack.  Different templates may declare pack parameters with the same
// short name; they are distinct entities.
//
// CBMC's "remove empty pack expansions" pass in
// `cpp_instantiate_template.cpp` used to collect short names
// *globally* across the `pack_size_map`, which accumulates entries
// from every template on the instantiation stack.  When the outer
// template on the stack had an empty pack named `_Types` and the
// inner template had a non-empty pack also named `_Types`, the
// inner template's function parameter that referenced its local
// `_Types` was wrongly stripped.
//
// This reduction mirrors the real MSVC `_Construct_in_place`
// failure which was itself triggered from inside
// `vector::_Emplace_back_with_unused_capacity` (an outer template
// instantiation whose pack happens to share the short name
// `_Types`).  The fix restricts the empty-pack short-name set to
// packs that are parameters of the CURRENT template being
// instantiated.

// Inner template: used to be stripped incorrectly.  It takes a
// value and a variadic pack, and just uses _Args' size.  Pre-fix
// this was fine on its own, but when called from an outer template
// that also has a pack named _Types, the inner's _Args parameter
// was dropped and `_Args` became unknown inside the body.
template <class _Ty, class... _Types>
_Ty inner(_Ty _Obj, _Types... _Args)
{
  (void)sizeof...(_Args);
  return _Obj;
}

// Outer template: has an empty pack called _Types.  Its
// instantiation is what places `_Types=0` into the shared
// pack_size_map.  Pre-fix, the outer's entry leaked into the
// inner's processing and caused inner's _Args to be stripped.
template <class... _Types>
int outer()
{
  // Call inner with a non-empty pack.  The inner's own _Types is
  // non-empty (size 1), but the outer's _Types is empty.  Pre-fix,
  // the short-name `_Types` in pack_size_map mapped to the outer's
  // empty pack, so inner's _Args was stripped.
  return inner(1, 2);
}

int main()
{
  int r = outer<>();
  __CPROVER_assert(
    r == 1, "nested pack short-name collision doesn't strip params");
  return 0;
}
