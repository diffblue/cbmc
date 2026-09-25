// C++11 ref-qualifiers on member function pointer types
// in template specializations
template <typename Sig>
struct traits;

template <typename R, typename C, typename... A>
struct traits<R (C::*)(A...)>
{
  static const int v = 0;
};

template <typename R, typename C, typename... A>
struct traits<R (C::*)(A...) const>
{
  static const int v = 1;
};

template <typename R, typename C, typename... A>
struct traits<R (C::*)(A...) &>
{
  static const int v = 2;
};

template <typename R, typename C, typename... A>
struct traits<R (C::*)(A...) &&>
{
  static const int v = 3;
};

int main()
{
  return 0;
}
