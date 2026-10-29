// N5008 [basic.start.dynamic]/1: a variable template specialization or a
// static data member of a class template specialization of class type is
// dynamically initialized (unordered) by its constructor, also when the
// specialization is first named in a function body.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int k;
  S(int x) : k(x + 1)
  {
  }
};
template <class T>
S direct(sizeof(T));
template <class T>
S copy = S(sizeof(T));
template <class T>
S braced{sizeof(T)};
template <class T>
auto deduced(S(sizeof(T) * 2));
template <class T>
struct X
{
  static S s;
};
template <class T>
S X<T>::s(sizeof(T) * 3);

template <class T, class U>
constexpr bool same = false;
template <class T>
constexpr bool same<T, T> = true;

int first_use()
{
  return deduced<char>.k;
}
int second_use()
{
  return deduced<char>.k + direct<char>.k;
}

int main()
{
  __CPROVER_assert(direct<char>.k == 2, "direct-initialization");
  __CPROVER_assert(copy<char>.k == 2, "copy-initialization");
  __CPROVER_assert(braced<char>.k == 2, "list-initialization");
  __CPROVER_assert(
    first_use() == 3 && same<decltype(deduced<char>), S>, "deduced type");
  __CPROVER_assert(second_use() == 5, "same specialization");
  __CPROVER_assert(X<char>::s.k == 4, "static data member");
  __CPROVER_assert(X<char>::s.k == 0, "WRONG (must FAIL)");
  return 0;
}
