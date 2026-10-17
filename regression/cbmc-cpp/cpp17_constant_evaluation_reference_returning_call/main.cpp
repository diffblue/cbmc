// N5008 [expr.const]/5: a call of a constexpr function returning a
// reference is a constant expression when the referenced object is
// ([meta.const.eval]/1: is_constant_evaluated() is true in it).  The shapes
// of libstdc++'s std::min, basic_string_view::operator[] and
// char_traits<char>::length.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
constexpr const T &min_of(const T &a, const T &b)
{
  return b < a ? b : a;
}
constexpr unsigned long clamp(unsigned long n)
{
  return min_of(n, 5ul);
}
struct S
{
  const char *p;
  constexpr const char &at(int i) const
  {
    return p[i];
  }
};
constexpr S s{"ab"};
constexpr unsigned long length(const char *str)
{
  if(__builtin_is_constant_evaluated())
  {
    unsigned long i = 0;
    while(str[i] != 0)
      ++i;
    return i;
  }
  return 0;
}
static_assert(clamp(4) == 4 && clamp(9) == 5, "std::min shape");
static_assert(s.at(1) == 'b' && S{"cd"}.at(0) == 'c', "operator[] shape");
static_assert(length("abc") == 3, "is_constant_evaluated");
template <unsigned long N = length("abcd")>
unsigned long g()
{
  return N;
}
int main()
{
  __CPROVER_assert(g() == 4, "default template argument");
  __CPROVER_assert(g() == 3, "WRONG (must FAIL)");
  return 0;
}
