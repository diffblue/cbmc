extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct remove_ref
{
  typedef T type;
};
template <class T>
struct remove_ref<T &>
{
  typedef T type;
};
template <class T>
struct remove_ref<T &&>
{
  typedef T type;
};
template <class T>
struct is_class_t
{
  static constexpr bool value = __is_class(T);
};
template <class T>
struct is_array_t
{
  static constexpr bool value = false;
};
template <class T, unsigned long N>
struct is_array_t<T[N]>
{
  static constexpr bool value = true;
};
namespace cust
{
// poison pills so that unqualified lookup does not find a std::begin
void begin(auto &) = delete;
void begin(const auto &) = delete;
struct decay_copy_t
{
  template <class T>
  constexpr typename remove_ref<T>::type operator()(T &&t) const
  {
    return static_cast<T &&>(t);
  }
} inline constexpr decay_copy{};
template <class T>
concept member_begin = requires(T & t)
{
  decay_copy(t.begin());
};
template <class T>
concept adl_begin =
  is_class_t<typename remove_ref<T>::type>::value && requires(T & t)
{
  decay_copy(begin(t));
};
struct begin_t
{
  template <class T>
    requires is_array_t<typename remove_ref<T>::type>::value ||
    member_begin<T> || adl_begin<T> constexpr auto operator()(T &&t) const
  {
    if constexpr(is_array_t<typename remove_ref<T>::type>::value)
      return t + 0;
    else if constexpr(adl_begin<T>)
      return decay_copy(begin(t));
    else
      return decay_copy(t.begin());
  }
} inline constexpr rbegin{};
} // namespace cust
template <class T>
concept range = requires(T & t)
{
  cust::rbegin(t);
};
template <range R>
constexpr int first_of(R &&r)
{
  return *cust::rbegin(r);
}
struct W
{
  int a[3];
  const int *begin() const
  {
    return a;
  }
};
int main()
{
  const int arr[4] = {1, 2, 3, 4};
  __CPROVER_assert(*cust::rbegin(arr) == 1, "array");
  W w{{7, 8, 9}};
  __CPROVER_assert(*cust::rbegin(w) == 7, "member begin");
  __CPROVER_assert(cust::decay_copy(w.a[1]) == 8, "decay_copy on an lvalue");
  __CPROVER_assert(first_of(arr) == 1, "constrained by a range concept");
  __CPROVER_assert(*cust::rbegin(arr) == 2, "WRONG (must FAIL)");
}
