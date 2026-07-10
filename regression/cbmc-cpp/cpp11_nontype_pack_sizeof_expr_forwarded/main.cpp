// N5008 [temp.variadic]/4-5: a pack expansion whose pattern is a `sizeof`
// unary-expression, `sizeof(Us)...`, forwarded from an enclosing function
// template, must expand to one element per pack member.
//
// KNOWNBUG: `box<sizeof(Us)...>::n` (with `box<int... Vs>` and
// `n = sizeof...(Vs)`) evaluated inside a function template `chk` that forwards
// its own pack `Us` yields the WRONG element count -- `chk((char)1,(char)2)`
// gives a value other than 2.  A member-value pattern `box<Trait<Us>::v...>::n`
// forwarded the same way DOES expand correctly (cpp11_nontype_value_pack_fn_
// template, CORE), so the defect is specific to a `sizeof(Us)...` (sizeof
// unary-expression) pack expansion pattern being forwarded.  g++/clang++
// compute 2.
//
// Residual non-type-pack defect surfaced while reproducing the tuple
// _TupleConstraints shape with a non-type proxy; the tuple uses TYPE packs and
// is not affected (cpp11_alias_template_parallel_pack is CORE).  Flip to CORE
// once a `sizeof(Us)...` pack expansion forwarded through a function template
// expands to the correct number of elements.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands.

extern "C" void __CPROVER_assert(int, const char *);

template <int... Vs>
struct box
{
  static constexpr int n = sizeof...(Vs);
};

template <class... Us>
constexpr int chk(Us...)
{
  return box<sizeof(Us)...>::n;
}

int main()
{
  __CPROVER_assert(
    chk((char)1, (char)2) == 2, "sizeof(Us)... forwarded expands to 2 elements");
  __CPROVER_assert(chk((char)1, (char)2) != 2, "WRONG must FAIL");
  return 0;
}
