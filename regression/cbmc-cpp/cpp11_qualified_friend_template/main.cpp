extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct vec
{
  T v[2];
  int size() const { return 2; }
};
namespace ns
{
namespace inner
{
template <class I, class A>
class results;
}
namespace det
{
template <class I, class A>
int algo(I s, inner::results<I, A> &m);
}
namespace inner
{
// N5008 [namespace.memdef]/3 + [temp.friend]/1: a friend declared with
// a QUALIFIED name refers to the template previously declared in that
// namespace (libstdc++ match_results befriending
// __detail::__regex_algo_impl).
template <class I, class A>
class results : private vec<I>
{
  typedef vec<I> _Unchecked;
  template <class I2, class A2>
  friend int det::algo(I2, results<I2, A2> &);
public:
  results() { this->v[0] = 5; }
};
} // namespace inner
namespace det
{
template <class I, class A>
int algo(I s, inner::results<I, A> &m)
{
  typename inner::results<I, A>::_Unchecked &res = m;
  return res.v[0] + res.size() + s;
}
} // namespace det
} // namespace ns
int main()
{
  ns::inner::results<int, char> r;
  __CPROVER_assert(ns::det::algo(1, r) == 8, "qualified friend template binds private-base reference");
  return 0;
}
