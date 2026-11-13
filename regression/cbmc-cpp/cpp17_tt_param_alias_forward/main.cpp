// Tests forwarding of an outer template's template-template
// parameter through a template alias to an inner template's
// template-template parameter — the pattern used by libstdc++'s
// `__detected_or_t<Default, Op, Args...>`:
//
//   template<typename _Default, template<typename...> class _Op,
//            typename... _Args>
//     using __detected_or_t
//       = typename __detected_or<_Default, _Op, _Args...>::type;
//
// Pre-fix: when the alias was instantiated with `_Op` bound to a
// class-scoped template alias (such as
// `__allocator_traits_base::__pointer<T> = typename T::pointer`),
// CBMC reported "expected template name for template template
// parameter" at the alias' definition line.  The argument
// arrived in `typecheck_template_args` as an `ambiguous` /
// `type_exprt` whose type was already a
// `template_parameter_symbol_type` (the resolved binding of the
// outer `_Op`); the binding code only looked at `cpp_name`-typed
// arguments and so produced an empty `template_name`, took no
// action, and reported the spurious error.
//
// The fix forwards the already-resolved
// `template_parameter_symbol_type` directly into `template_map`
// and replaces the un-normalised `ambiguous` arg with a
// `type_exprt` so downstream `template_suffix` (which has a
// strict `expr.id() != ID_ambiguous` invariant) doesn't trip.

template <
  typename _Default,
  template <typename...>
  class _Op,
  typename... _Args>
struct __detected_or
{
  using type = _Default;
};

template <
  typename _Default,
  template <typename...>
  class _Op,
  typename... _Args>
using __detected_or_t = typename __detected_or<_Default, _Op, _Args...>::type;

struct base
{
protected:
  template <typename _Tp>
  using __pointer = typename _Tp::pointer;
};

template <typename _Alloc>
struct alloc_traits : base
{
  using pointer = __detected_or_t<int *, __pointer, _Alloc>;
};

struct allocator_with_pointer
{
  using pointer = float *;
};

int main()
{
  using P = alloc_traits<allocator_with_pointer>::pointer;
  P p = nullptr;
  __CPROVER_assert(sizeof(p) >= 0, "TT-param alias forwarding works");
  return 0;
}
