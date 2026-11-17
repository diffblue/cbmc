// N5008 [temp.spec.partial.match], [temp.arg.explicit]/4: for three
// arguments the specialization or_<B1, B2, B3, Bn...> matches with Bn the
// empty pack, and is instantiated with those three arguments.  The shape of
// libstdc++ 11's __or_ and __is_one_of in <charconv>'s
// __integer_to_chars_result_type (to_chars), where the match is the last of
// six alternatives.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool v>
struct bc
{
  static constexpr bool value = v;
};
template <bool, class A, class B>
struct cond
{
  typedef B type;
};
template <class A, class B>
struct cond<true, A, B>
{
  typedef A type;
};
template <class...>
struct or_;
template <class B1, class B2>
struct or_<B1, B2> : cond<B1::value, B1, B2>::type
{
};
template <class B1, class B2, class B3, class... Bn>
struct or_<B1, B2, B3, Bn...> : cond<B1::value, B1, or_<B2, B3, Bn...>>::type
{
};
template <class A, class B>
struct same : bc<false>
{
};
template <class A>
struct same<A, A> : bc<true>
{
};
template <class T, class... Ts>
using one_of = or_<same<T, Ts>...>;
template <class T>
using is_s = one_of<T, signed char, short, int>;
template <class T>
using is_u = one_of<
  T,
  unsigned char,
  unsigned short,
  unsigned,
  unsigned long,
  unsigned long long,
  long double>;
template <bool, class T>
struct en
{
};
template <class T>
struct en<true, T>
{
  typedef T type;
};
struct res
{
  int v;
};
template <class T>
using rt = typename en<or_<is_s<T>, is_u<T>, same<char, T>>::value, res>::type;
template <class T>
rt<T> g(char *, char *, T x, int)
{
  return res{(int)x};
}
int main()
{
  char a, b;
  __CPROVER_assert(
    g(&a, &b, (long double)3, 10).v == 3, "the last alternative");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
