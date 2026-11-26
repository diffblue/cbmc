extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct one
{
  T v;
  static constexpr int size = 1;
};
template <class T, class U>
struct two
{
  T v;
  U w;
  static constexpr int size = 2;
};
// type-parameter-key `typename' for a template template parameter, also
// for a pack and with a default argument
template <template <class> typename C>
struct use
{
  C<int> c;
  int size() const
  {
    return C<int>::size;
  }
};
template <template <class...> typename C, class... Ts>
int pack_size()
{
  return C<Ts...>::size;
}
template <template <class> typename C = one>
struct with_default
{
  C<char> c;
};
int main()
{
  use<one> u;
  u.c.v = 3;
  __CPROVER_assert(u.size() == 1 && u.c.v == 3, "template template parameter");
  __CPROVER_assert(pack_size<two, int, char>() == 2, "variadic");
  with_default<> d;
  d.c.v = 'x';
  __CPROVER_assert(d.c.v == 'x', "default argument");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
