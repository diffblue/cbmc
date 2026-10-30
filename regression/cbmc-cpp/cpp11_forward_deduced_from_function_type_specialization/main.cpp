extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct remove_reference
{
  using type = T;
};
template <class T>
struct remove_reference<T &>
{
  using type = T;
};
template <class T>
struct remove_reference<T &&>
{
  using type = T;
};
template <class T>
constexpr T &&forward(typename remove_reference<T>::type &t) noexcept
{
  return static_cast<T &&>(t);
}
template <class Sig>
struct function;
template <class R, class... ArgTypes>
struct function<R(ArgTypes...)>
{
  R (*fp)(ArgTypes...);
  R operator()(ArgTypes... args) const
  {
    return fp(forward<ArgTypes>(args)...);
  }
};
int add_one(const int &x)
{
  return x + 1;
}
int main()
{
  function<int(const int &)> g{add_one};
  __CPROVER_assert(
    g(41) == 42,
    "forward<const int &> through a partial specialization over a function "
    "type");
  __CPROVER_assert(g(41) == 43, "WRONG (must FAIL)");
}
