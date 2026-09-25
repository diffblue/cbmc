// The GCC/Clang class-property type traits behind <type_traits>:
// N5008 [meta.unary.prop] is_empty, is_polymorphic, has_virtual_destructor,
// is_standard_layout, is_aggregate, is_literal_type (and is_pod,
// [depr.meta.types]).  Every one was unconditionally false, so libstdc++'s
// `__by_ref_or_value_fn' (predefined_ops.h: hold an EMPTY functor by value,
// anything else by reference) stored std::equal_to<> by reference to a
// temporary and std::find over a vector compared against garbage.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct E2 : E
{
  void f();
  static int s;
  using type = int;
};
struct N
{
  int x;
};
struct NE : E
{
  int y;
};
struct P
{
  virtual void f();
};
struct PD : P
{
};
struct VD
{
  virtual ~VD();
};
struct VB : virtual E
{
};
struct Ref
{
  int &r;
};
struct Mixed
{
public:
  int a;

private:
  int b;
};
struct Ctor
{
  Ctor(int);
  int x;
};
struct PrivBase : private N
{
};
struct Dtor
{
  ~Dtor();
  int x;
};
union U
{
  int a;
  float b;
};
struct Lit
{
  constexpr Lit(int v) : x(v)
  {
  }
  int x;
};
static_assert(__is_empty(E) && __is_empty(E2), "empty");
static_assert(
  !__is_empty(N) && !__is_empty(NE) && !__is_empty(P) && !__is_empty(U) &&
    !__is_empty(VB) && !__is_empty(int),
  "not empty");
static_assert(
  __is_polymorphic(P) && __is_polymorphic(PD) && __is_polymorphic(VD),
  "polymorphic");
static_assert(
  !__is_polymorphic(N) && !__is_polymorphic(E) && !__is_polymorphic(int),
  "not polymorphic");
static_assert(
  __has_virtual_destructor(VD) && !__has_virtual_destructor(P) &&
    !__has_virtual_destructor(N),
  "virtual destructor");
static_assert(
  __is_standard_layout(N) && __is_standard_layout(E) &&
    __is_standard_layout(U) && __is_standard_layout(int) &&
    __is_standard_layout(int[3]),
  "standard layout");
static_assert(
  !__is_standard_layout(P) && !__is_standard_layout(Mixed) &&
    !__is_standard_layout(Ref) && !__is_standard_layout(VB),
  "not standard layout");
static_assert(__is_pod(N) && __is_pod(int) && __is_pod(U), "pod");
static_assert(!__is_pod(P) && !__is_pod(Ctor) && !__is_pod(Dtor), "not pod");
static_assert(
  __is_aggregate(N) && __is_aggregate(NE) && __is_aggregate(U) &&
    __is_aggregate(int[2]) && __is_aggregate(Ref),
  "aggregate");
static_assert(
  !__is_aggregate(P) && !__is_aggregate(Ctor) && !__is_aggregate(Mixed) &&
    !__is_aggregate(PrivBase) && !__is_aggregate(int),
  "not aggregate");
static_assert(
  __is_literal_type(N) && __is_literal_type(Lit) && __is_literal_type(int) &&
    __is_literal_type(void),
  "literal");
static_assert(
  !__is_literal_type(Dtor) && !__is_literal_type(VD),
  "not literal");

// the predefined_ops.h shape: an empty functor held by value, a non-empty one
// by reference; the trait asked inside a template instantiation of a class
// whose explicit specialization has not been elaborated yet
template <bool>
struct conditional_
{
  template <class T, class>
  using type = T;
};
template <>
struct conditional_<false>
{
  template <class, class F>
  using type = F;
};
template <bool C, class T, class F>
using conditional_t = typename conditional_<C>::template type<T, F>;
template <class T>
struct is_empty
{
  static constexpr bool value = __is_empty(T);
};
template <class T = void>
struct equal_to;
template <>
struct equal_to<void>
{
  template <class T, class U>
  constexpr bool operator()(T &&t, U &&u) const
  {
    return t == u;
  }
};
template <class F>
using by_ref_or_value = conditional_t<is_empty<F>::value, F, F &>;
template <class Func, class Value>
struct comp_with_val
{
  using Fn = by_ref_or_value<Func>;
  explicit constexpr comp_with_val(Fn f, const Value &v) : m_f(f), m_val(v)
  {
  }
  [[__no_unique_address__]] Fn m_f;
  const Value &m_val;
  template <class T>
  constexpr bool operator()(T &&arg)
  {
    return m_f(arg, m_val);
  }
};
template <class Value>
constexpr comp_with_val<equal_to<>, Value> equal_to_val(const Value &val)
{
  return comp_with_val<equal_to<>, Value>(equal_to<>(), val);
}
template <class It, class Pred>
constexpr It find_if(It first, It last, Pred pred)
{
  while(first != last && !pred(*first))
    ++first;
  return first;
}
template <class It, class T>
constexpr It find(It first, It last, const T &val)
{
  return find_if(first, last, equal_to_val(val));
}
int main()
{
  int a[3] = {1, 2, 3};
  int *it = find(a, a + 3, 2);
  __CPROVER_assert(it == a + 1 && *it == 2, "find through an empty functor");
  static_assert(
    __is_same(decltype(equal_to_val(1).m_f), equal_to<>),
    "empty functor held by value");
  __CPROVER_assert(it == a + 2, "WRONG (must FAIL)");
}
