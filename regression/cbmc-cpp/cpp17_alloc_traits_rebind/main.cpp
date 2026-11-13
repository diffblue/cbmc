// Tests `_Tp::template rebind<_Up>::other`-style qualified-name
// lookup as used in libstdc++'s
// `__allocator_traits_base::__rebind` partial-spec evaluation.
// Multiple unrelated allocator instantiations live in the program
// and each has its own `rebind` member template.  Per
// [basic.lookup.qual], the lookup of `rebind` after `_Alloc::`
// must be restricted to `_Alloc`'s own scope (and base classes),
// not to every same-base-name template across the program.
//
// Pre-fix CBMC issued "template scope 'rebind' is ambiguous" with
// candidates from every `allocator<X>` and every `__alloc_traits<X>`
// instantiation, because:
//
// 1. The TT-param-bound `_Tp` was rewritten to bare "allocator" by
//    `template_mapt::apply` (instead of being replaced with the
//    full struct_tag identifier of the bound instance) when the
//    cpp_name was a QUALIFIED form like `_Tp::rebind<_Up>::other`.
// 2. `disambiguate_template_classes` then fell back to a root-
//    scope-recursive search, which gathered every `rebind` in the
//    program.

template <typename _Tp>
struct __new_allocator
{
  template <typename _Up>
  struct rebind
  {
    using other = __new_allocator<_Up>;
  };
};

template <typename _Tp>
struct allocator : public __new_allocator<_Tp>
{
  template <typename _Up>
  struct rebind
  {
    using other = allocator<_Up>;
  };
};

// Pre-existing allocator instances that exercise the would-be
// ambiguity (their `rebind` members would have been collected by
// the wrong root-recursive fallback).
allocator<char> ac;
allocator<int> ai;
allocator<long> al;
__new_allocator<char> nac;

// Mimic __allocator_traits_base::__rebind partial spec evaluation
template <typename _Tp, typename _Up>
struct __rebind
{
  using type = typename _Tp::template rebind<_Up>::other;
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
  using R = typename __rebind<allocator<A>, B>::type;
  R r;
  // R must be allocator<B>, so R::value_type == B (no a_field).
  // We can't easily access value_type in this test (allocator has
  // no value_type member), so we just check that the type
  // resolves and is a complete class.
  __CPROVER_assert(sizeof(r) >= 0, "rebind chain resolved");
  return 0;
}
