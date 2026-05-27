// Negative companion to cpp17_replace_first_arg: ensures that
// `__replace_first_arg<allocator<A>, B>::type::value_type` does NOT
// equal `A`.  Uses a static_assert on `sizeof(value_type)` to catch
// the misidentification at translation time.  Pre-fix R::value_type
// = A (size 4 — has int a_field); post-fix R::value_type = B (size 4
// too — coincidence in this minimal repro).  Use a different layout:
// give A a different size so the static_assert is a sharp test.

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
  int a1, a2, a3; // size 12 (3 ints)
};
struct B
{
  char b; // size 1 (with padding it's 1)
};

int main()
{
  using R = typename __replace_first_arg<allocator<A>, B>::type;
  R x;
  typename R::value_type y;
  // R must be allocator<B>, so R::value_type = B (sizeof = 1, not 12).
  __CPROVER_assert(
    sizeof(y) == sizeof(B), "rebind through TT param yields B");
  __CPROVER_assert(sizeof(y) != sizeof(A), "rebind not stale at A");
  return 0;
}
