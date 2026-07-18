// N5008 [class.qual], [temp.inst]/2: instantiating __alloc_traits<int>
// must give it the member `value_type` whose type is spelled through
// the qualified typedef-name _Base_type::value_type.
//
// KNOWNBUG: during implicit instantiation of __alloc_traits<int>
// (triggered from the __uset_hashtable alias chain below), converting
// the member declaration `_Base_type::value_type value_type;` throws
// inside the C++ front end; per-member error recovery
// ([temp.inst]/11 tolerance in typecheck_compound_body) now keeps the
// REST of the class intact, but this member is silently dropped:
// `at.value_type` fails with "symbol 'value_type' is unknown" and
// main's body is left incomplete (vacuously green).  Reduced by cvise
// from the 39-line cpp17_member_template_completed_instance test (the
// same mid-body throw that used to drop ALL later members there).
//
// g++/clang++ accept and verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

template <int __v>
struct integral_constant
{
  static constexpr int value = __v;
};
template <bool __v>
using __bool_constant = integral_constant<__v>;
template <typename>
struct __not_ : __bool_constant<!bool()>
{
};
template <typename>
struct hash;
struct allocator_traits
{
  using value_type = int;
};
template <typename = int>
struct __alloc_traits
{
  typedef allocator_traits _Base_type;
  _Base_type::value_type value_type; // dropped during instance conversion
};
template <typename _Tp, typename>
using __cache_default = __not_<_Tp>;
template <bool>
using __uset_traits = int;
template <
  typename _Value,
  typename _Hash,
  typename = __uset_traits<__cache_default<_Value, _Hash>::value>>
using __uset_hashtable = int;
template <typename _Hash = hash<int>, typename _Alloc = int>
struct unordered_set
{
  __uset_hashtable<_Hash, int> _Hashtable;
};
template <typename>
struct vector
{
  __alloc_traits<> _Tp_alloc_type;
};
template <typename _Alloc>
struct hash<vector<_Alloc>>;

int main()
{
  unordered_set<> s;
  __alloc_traits<> at;
  at.value_type = 5;
  __CPROVER_assert(at.value_type == 5, "qualified-typedef member usable");
  return 0;
}
