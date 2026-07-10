// N5008 [temp.alias]/2 + [temp.variadic]/4-5: instantiating an alias template
// whose body is a pack expansion (`sum_t<sizeof(Us)...>`) with a pack that is
// FORWARDED from an enclosing function template (`sums<Us...>` where `Us` is the
// caller's own pack) must, at the alias's point of use, expand the body against
// the concrete pack and fold the resulting constant.
//
// KNOWNBUG: CBMC fails to fold `sums<Us...>::v` when `sums` is a pack-expansion
// alias template and `Us` is forwarded from the enclosing function template
// `chk`.  `chk((char)1, (char)2)` should be a constant 2 (sizeof(char) == 1,
// summed over two elements), and g++/clang++ compute 2, but CBMC leaves the
// result unconstrained (the assertion can fail).  The same alias used with
// EXPLICIT concrete arguments at namespace scope
// (`sums<char,char>::v`) folds correctly; only the forwarded-pack instantiation
// inside a function template is affected.  A non-pack-expansion alias
// (`using al = box<U>;`) forwards and folds fine, so the defect is specific to
// a pack-expansion alias body instantiated with a forwarded pack.
//
// This masks the (separately fixed) two-parallel-pack member-alias expansion
// (cpp11_alias_template_parallel_pack) and is a residual blocker for
// std::tuple's _TupleConstraints (`__and_<is_X<_Types,_UTypes>...>` accessed as
// a value/type after being instantiated with a forwarded pack).  A class
// template around the alias is NOT required (this free-function form is the
// minimal trigger).
//
// Flip to CORE once a pack-expansion alias template folds when instantiated with
// a forwarded parameter pack.
// Non-vacuity: assertion 2 ("WRONG must FAIL") must FAIL when the fix lands
// (chk() == 2).

extern "C" void __CPROVER_assert(int, const char *);

template <unsigned...>
struct sum_t;
template <>
struct sum_t<>
{
  static constexpr unsigned v = 0;
};
template <unsigned H, unsigned... T>
struct sum_t<H, T...>
{
  static constexpr unsigned v = H + sum_t<T...>::v;
};

template <class... Us>
using sums = sum_t<sizeof(Us)...>;

template <class... Us>
constexpr unsigned chk(Us...)
{
  return sums<Us...>::v;
}

int main()
{
  __CPROVER_assert(
    chk((char)1, (char)2) == 2,
    "pack-expansion alias folds with a forwarded pack");
  __CPROVER_assert(chk((char)1, (char)2) != 2, "WRONG must FAIL");
  return 0;
}
