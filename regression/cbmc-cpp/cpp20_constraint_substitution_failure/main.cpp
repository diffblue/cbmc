// N5008 [temp.constr.atomic]/3: if substituting into an atomic
// constraint's parameter mapping fails, the constraint is NOT
// satisfied -- it is not an error.  Here common_reference_t<T,U>
// (whose primary template has no ::type, mirroring libc++'s
// common_reference when none exists) fails to substitute inside
// same_as's argument, so common_reference_with<int,int> must be
// FALSE and the unconstrained use() overload must win (g++ and
// clang++ return 42).  CBMC selects the CONSTRAINED overload
// (wrong code, returns 41).  In full libc++ <vector> builds the same
// machinery surfaces as a hard "found no match for symbol 'same_as'"
// inside reverse_iterator's iterator_concept; root of the cpp20
// *_libcxx failures (vector/map/ranges/erase_if/initializer_list).
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, class U>
concept same_as = __is_same(T, U);

template <class...>
struct common_reference
{
  // primary: no ::type (mirrors libc++ when no common reference exists)
};

template <class... Ts>
using common_reference_t = typename common_reference<Ts...>::type;

template <class T, class U>
concept common_reference_with = same_as<U, common_reference_t<T, U>>;

template <class T>
int use(T v) requires common_reference_with<T, T>
{
  return v;
}

template <class T>
int use(T v)
{
  return v + 1;
}

int main()
{
  // common_reference_t<int,int> has no ::type: substitution failure in
  // the concept's argument makes the constraint UNSATISFIED
  // ([temp.constr.atomic]/3), so the unconstrained overload wins.
  __CPROVER_assert(use(41) == 42, "unsatisfied constraint, not an error");
  return 0;
}
