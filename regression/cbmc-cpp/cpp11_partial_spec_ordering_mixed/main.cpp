extern "C" void __CPROVER_assert(bool, const char *);
// specializations declared most-specialized first (reverse of ps1)
template <class T>
struct tr
{
  static int w()
  {
    return 0;
  }
};
template <class T>
struct tr<const T *>
{
  static int w()
  {
    return 2;
  }
};
template <class T>
struct tr<T *>
{
  static int w()
  {
    return 1;
  }
};
// T vs T* vs T**
template <class T>
struct dp
{
  static int w()
  {
    return 0;
  }
};
template <class T>
struct dp<T *>
{
  static int w()
  {
    return 1;
  }
};
template <class T>
struct dp<T **>
{
  static int w()
  {
    return 2;
  }
};
// template-id pattern vs bare parameter; fixed arity over pack
template <class... X>
struct pack
{
};
template <class T>
struct un
{
  static int w()
  {
    return 0;
  }
};
template <class... X>
struct un<pack<X...>>
{
  static int w()
  {
    return 1;
  }
};
template <class A, class B>
struct un<pack<A, B>>
{
  static int w()
  {
    return 2;
  }
};
// reference vs const reference
template <class T>
struct rf
{
  static int w()
  {
    return 0;
  }
};
template <class T>
struct rf<T &>
{
  static int w()
  {
    return 1;
  }
};
template <class T>
struct rf<const T &>
{
  static int w()
  {
    return 2;
  }
};
int main()
{
  __CPROVER_assert(
    tr<const int *>::w() == 2, "const T* over T* (reversed decl order)");
  __CPROVER_assert(tr<int *>::w() == 1, "T* over T");
  __CPROVER_assert(tr<int>::w() == 0, "T");
  __CPROVER_assert(dp<int **>::w() == 2, "T** over T*");
  __CPROVER_assert(dp<int *>::w() == 1, "T* over T");
  __CPROVER_assert(un<pack<int, char>>::w() == 2, "pack<A,B> over pack<X...>");
  __CPROVER_assert(un<pack<int>>::w() == 1, "pack<X...> over T");
  __CPROVER_assert(un<int>::w() == 0, "primary");
  __CPROVER_assert(rf<const int &>::w() == 2, "const T& over T&");
  __CPROVER_assert(rf<int &>::w() == 1, "T& over T");
  return 0;
}
