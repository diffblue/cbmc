// N5008 [temp.variadic]/4-5: a pack expansion `P...` expands to one element per
// element of the pack `P`, whether `P` is a type or a NON-type parameter pack.
//
// KNOWNBUG (canonical root of the non-type-pack family): forwarding a NON-type
// parameter pack `T...` from one template into another template-argument list
// COLLAPSES for two or more elements.  `fwd<2,3>` forwards `T = <2,3>` to
// `cnt<T...>`, which should be `cnt<2,3>` with `sizeof...(V) == 2`; CBMC yields
// 1 (the pack collapses to a single element).  A ONE-element pack works
// (`fwd<5>::n == 1`), because a single-element pack is additionally recorded as
// a scalar `type_map` entry; a direct `cnt<2,3>::n` works too.
//
// Root cause (see findings): template_mapt stores a type parameter pack's
// element TYPES in `pack_args_map`, but has no storage for a NON-type pack's
// element VALUES -- `template_mapt::build` collects a pack element only when its
// argument `id() == ID_type`, and a non-type pack's arguments are constants.
// So `pack_args_map` is empty for a non-type pack (only its size is recorded),
// and the substitution expander cannot expand `T...` to the concrete elements.
// The defect is masked whenever both sides of a comparison collapse equally
// (e.g. libc++'s `__is_same(dummy<Pred...>, dummy<((void)Pred, true)...>)`,
// regression test libcxx_comma_in_template_arg) but is exposed by any read of
// the count or of an element value.  It is the shared root of
// cpp11_nontype_pack_recursive_two_elem, cpp11_nontype_pack_sizeof_expr_
// forwarded, and cpp17_tuple_get_two_pack_ctor_3elem.
//
// A COMPLETE fix must (1) store non-type pack element values (a
// `pack_expr_map`), (2) expand them consistently in BOTH the bare-pack and the
// nested-pattern expander branches (a partial fix of only the bare branch makes
// the two sides of `__is_same` disagree and regresses
// libcxx_comma_in_template_arg), and (3) bind the per-element value in the
// nested-pattern element map.  g++ and clang++ compute 2.
//
// Flip to CORE once a forwarded non-type parameter pack of >= 2 elements
// expands to the correct number of elements.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands.

extern "C" void __CPROVER_assert(int, const char *);

template <int... V>
struct cnt
{
  static constexpr int n = sizeof...(V);
};

template <int... T>
struct fwd
{
  static constexpr int n = cnt<T...>::n;
};

int main()
{
  __CPROVER_assert(fwd<2, 3>::n == 2, "forwarded non-type pack keeps 2 elements");
  __CPROVER_assert(fwd<2, 3>::n != 2, "WRONG must FAIL");
  return 0;
}
