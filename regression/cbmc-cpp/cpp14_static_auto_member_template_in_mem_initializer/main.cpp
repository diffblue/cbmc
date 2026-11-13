extern "C" void __CPROVER_assert(bool, const char *);
struct sv
{
  const char *p;
  unsigned n;
  using value_type = char;
  const char *data() const
  {
    return p;
  }
  unsigned size() const
  {
    return n;
  }
};
struct wsv
{
  const wchar_t *p;
  unsigned n;
  using value_type = wchar_t;
  const wchar_t *data() const
  {
    return p;
  }
  unsigned size() const
  {
    return n;
  }
};
struct str
{
  char buf[16];
  unsigned len;
  str() : len(0)
  {
  }
  str(sv s) : len(s.n)
  {
    for(unsigned i = 0; i < s.n; ++i)
      buf[i] = s.p[i];
  }
};
class path
{
public:
  using value_type = char;
  template <class Source>
  path(const Source &source) : m_pathname(_S_convert(source))
  {
  }
  unsigned size() const
  {
    return m_pathname.len;
  }

private:
  str m_pathname;
  template <class T>
  static auto _S_convert(T s)
  {
    if constexpr(__is_same(typename T::value_type, value_type))
      return s;
    else
      return _S_convert(s.data(), s.data() + s.size());
  }
  template <class E>
  static auto _S_convert(const E *first, const E *last);
};
template <class E>
auto path::_S_convert(const E *first, const E *last)
{
  static char tmp[16];
  unsigned n = 0;
  for(; first != last; ++first)
    tmp[n++] = static_cast<char>(*first);
  return sv{tmp, n};
}
int main()
{
  sv s{"abc", 3};
  path p(s);
  __CPROVER_assert(p.size() == 3, "same char type");
  wsv w{L"de", 2};
  path q(w);
  __CPROVER_assert(
    q.size() == 2, "converted through the out-of-line auto member template");
  __CPROVER_assert(q.size() == 3, "WRONG (must FAIL)");
}
