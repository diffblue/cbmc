// Tests that a partial specialization with a template-template parameter
// bound to a class-template instance correctly substitutes the template's
// name (not the whole instance) when the spec body uses the TT param with
// fresh template arguments.  Mirrors libstdc++'s `__replace_first_arg`
// pattern used by `__alloc_rebind`:
//
//   template <typename _Tp, typename _Up>
//   struct __replace_first_arg { };
//
//   template <template <typename, typename...> class _SomeTemplate,
//             typename _Up, typename _Tp, typename... _Types>
//   struct __replace_first_arg<_SomeTemplate<_Tp, _Types...>, _Up>
//   { using type = _SomeTemplate<_Up, _Types...>; };
//
// For `__replace_first_arg<allocator<A>, B>::type`:
//
// - the TT parameter `_SomeTemplate` deduces to the bound `allocator`
//   template (CBMC currently records the WHOLE struct_tag for the
//   instance), and
// - the variadic pack `_Types...` deduces to an EMPTY pack;
//
// the spec body's `using type = _SomeTemplate<_Up, _Types...>` must
// substitute the TT name (yielding `allocator<_Up, _Types...>`) and
// then expand `_Up = B`, `_Types... = ()` to produce `allocator<B>`,
// not the original instance `allocator<A>`.
//
// Once `R = allocator<B>` is obtained, accessing `R::value_type` must
// resolve to `B` even though the outer spec's instantiation has its
// own `_Tp` bound to `A`: the inner allocator instantiation's
// `_Tp = B` must shadow the outer's `_Tp = A`.

template <typename _Tp, typename _Up>
struct __replace_first_arg
{ };

template <template <typename, typename...> class _SomeTemplate,
          typename _Up, typename _Tp, typename... _Types>
struct __replace_first_arg<_SomeTemplate<_Tp, _Types...>, _Up>
{
  using type = _SomeTemplate<_Up, _Types...>;
};

template <typename _Tp>
struct allocator
{
  using value_type = _Tp;
};

struct A
{
  int a_field;
};
struct B
{
  int b_field;
};

int main()
{
  using R = typename __replace_first_arg<allocator<A>, B>::type;
  R x;
  // R must be allocator<B>, so R::value_type must be B (which has
  // b_field, not a_field).
  typename R::value_type y;
  y.b_field = 42;
  __CPROVER_assert(y.b_field == 42, "rebind through TT param yields B");
  return 0;
}
