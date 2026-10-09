// N5008 [basic.lookup.qual] + [temp.names]/3: in `T::template name<args>`
// the name is looked up in the scope of T only.
//
// This used to fail ("template scope 'rebind' is ambiguous"): a
// mid-body conversion throw during implicit instantiation silently
// dropped every subsequent member -- including the member class
// template, whose absence from the instance scope made the fallback
// collect every same-name member template program-wide.  Fixed by
// per-member error recovery ([temp.inst]/11 tolerance) in
// typecheck_compound_body.  Root cause of cpp17_hash_node_vector_alloc
// (unordered_set's hash-node allocator machinery followed by
// vector<K>): this is that test reduced by cvise to 39 header-free
// lines (the alias chain mirrors libstdc++'s __uset_hashtable and the
// hash<vector<...>> partial-specialization declaration; each part is
// needed to reproduce the instantiation order).
//
// g++/clang++ accept and verify at runtime.
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
template <typename>
struct allocator
{
  template <typename>
  struct rebind;
};
struct allocator_traits
{
  using value_type = int;
};
struct K;
template <typename = int>
struct __alloc_traits
{
  typedef allocator_traits _Base_type;
  _Base_type::value_type value_type;
  template <typename>
  struct rebind
  {
    typedef int other;
  };
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
template <typename _Hash = hash<K>, typename _Alloc = int>
struct unordered_set
{
  __uset_hashtable<_Hash, int> _Hashtable;
};
template <typename>
struct _Vector_base
{
  __alloc_traits<>::rebind<int>::other _Tp_alloc_type;
};
template <typename _Tp, typename = allocator<_Tp>>
struct vector : _Vector_base<_Tp>
{
};
template <typename _Alloc>
struct hash<vector<_Alloc>>;

int main()
{
  unordered_set<> s;
  s._Hashtable = 3;
  vector<K> v;
  v._Tp_alloc_type = 4;
  __CPROVER_assert(
    s._Hashtable == 3 && v._Tp_alloc_type == 4, "members usable");
  return 0;
}
