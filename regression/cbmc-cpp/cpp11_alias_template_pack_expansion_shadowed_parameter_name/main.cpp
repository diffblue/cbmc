// N5008 [temp.alias]/2, [temp.variadic]/5: `typename id<A>::type...' in an
// alias template expands the alias's own pack A, whatever the parameters of
// the template using the alias are called
extern "C" void __CPROVER_assert(bool, const char *);
template <class C, class... A>
struct holder
{
  template <class S>
  holder(const S &) : count(sizeof...(A)), last_size(0)
  {
    int sizes[] = {0, int(sizeof(A))...};
    last_size = sizes[sizeof...(A)];
  }
  int count;
  int last_size;
};
template <class T>
struct id
{
  using type = T;
};
template <class... A>
using holder_of = holder<char, typename id<A>::type...>;
template <class... A>
int last_size(holder_of<A...> h, A &&...)
{
  return h.last_size;
}
template <class... A>
struct count
{
  static const int value = sizeof...(A);
};
template <class... A>
using pointers_to = count<typename id<A *>::type...>;
template <class... A>
int pointer_count(A...)
{
  return pointers_to<A...>::value;
}
int main()
{
  int i = 1;
  long l = 2;
  __CPROVER_assert(last_size("ab", i, l) == sizeof(long &), "pack expanded");
  __CPROVER_assert(pointer_count(i, l, 'c') == 3, "nested in a compound type");
  __CPROVER_assert(last_size("ab", i, l) == 0, "WRONG (must FAIL)");
}
