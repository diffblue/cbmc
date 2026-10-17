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
struct holder
{
  char name[4];
  template <class A>
  holder(A &&a) : name{}
  {
    const char(&src)[4] = forward<A>(a);
    for(int i = 0; i < 4; ++i)
      name[i] = src[i];
  }
};
int main()
{
  const char text[4] = "abc";
  const char(&r)[4] = static_cast<const char(&)[4]>(text);
  __CPROVER_assert(
    r[2] == 'c', "direct static_cast to a reference-to-array type");
  holder h("abc");
  __CPROVER_assert(
    h.name[0] == 'a' && h.name[2] == 'c' && h.name[3] == 0,
    "forward of an array lvalue keeps the array reference type");
  __CPROVER_assert(h.name[1] == 'c', "WRONG (must FAIL)");
}
