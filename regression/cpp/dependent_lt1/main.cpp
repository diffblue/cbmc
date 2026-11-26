// C++11: '<' after dependent qualified name is less-than, not template bracket
template <typename T, T v>
struct integral_constant
{
  static constexpr T value = v;
};

// T::member < expr in base specifier
template <typename R1, typename R2>
  struct less_impl : integral_constant < bool,
  R1::num<R2::num>
{
};

// Template-id qualifier: Wrapper<R>::value < expr
template <typename T>
struct Wrapper
{
  static const int value = 0;
};
template <typename R>
  struct X : integral_constant < bool,
  Wrapper<R>::value<5>
{
};

// In typedef context
template <typename R>
struct Y
{
  typedef integral_constant < bool, R::a<R::b> type;
};

// ::template keyword overrides the disambiguation
struct A
{
  template <typename T, typename U>
  using type = T;
};
template <bool C>
struct cond
{
};
template <>
struct cond<true> : A
{
};
template <bool C, typename T, typename U>
using cond_t = typename cond<C>::template type<T, U>;

int main()
{
  return 0;
}
