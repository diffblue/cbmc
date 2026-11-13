// N5008 [expr.const]/10.16 (C++14 relaxed constexpr): a constexpr function may
// define a local variable of literal class type, and call its constructor
// and its member functions, also ones that modify it.  The result is a
// constant expression, usable as a template argument (libstdc++ 16's
// __literal_encoding_is_unicode<wchar_t>(), which builds a string_view).
#include <string_view>
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  int n;
  constexpr S(const char *p) : n(0)
  {
    while(p[n])
      ++n;
  }
  constexpr int size() const
  {
    return n;
  }
  constexpr void cut(int k)
  {
    n -= k;
  }
  constexpr void cut_twice()
  {
    cut(1);
    cut(1);
  }
};

constexpr int own_class()
{
  S s("abcd");
  s.cut_twice();
  return s.size();
}

constexpr bool with_string_view()
{
  std::string_view s("UTF-32LE");
  s.remove_prefix(4);
  if(s.ends_with("LE") || s.ends_with("BE"))
    s.remove_suffix(2);
  return s == "32";
}

template <int N, bool B>
int value()
{
  return B ? N : -1;
}

int main()
{
  static_assert(own_class() == 2, "");
  static_assert(with_string_view(), "");
  __CPROVER_assert(
    (value<own_class(), with_string_view()>() == 2), "template arguments");
  __CPROVER_assert(own_class() == 2, "run time");
  __CPROVER_assert(own_class() == 4, "WRONG (must FAIL)");
}
