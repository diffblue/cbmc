extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct traits;
template <class T>
struct traits<T *>
{
  typedef T value_type;
  static int which()
  {
    return 1;
  }
};
template <class T>
struct traits<const T *>
{
  typedef T value_type;
  static int which()
  {
    return 2;
  }
};
template <class T>
struct is_const_t
{
  static const bool value = false;
};
template <class T>
struct is_const_t<const T>
{
  static const bool value = true;
};
template <class It>
struct exec
{
  typedef typename traits<It>::value_type char_t;
  static bool ok()
  {
    return !is_const_t<char_t>::value;
  }
};
int main()
{
  __CPROVER_assert(
    traits<const char *>::which() == 2,
    "const T* specialization is more specialized");
  __CPROVER_assert(exec<const char *>::ok(), "value_type strips const");
  return 0;
}
