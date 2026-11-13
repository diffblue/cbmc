// N5008 [over.ics.list]/7, [dcl.init.list]/5: `run({"cl", "@" + name()})'
// for a parameter whose class has an initializer-list constructor converts
// each element to the element type.  The element `"@" + name()' is
// type-checked once -- its `str &&' parameter binds the call result as an
// xvalue.  The viability check of the initializer-list constructor
// type-checked the resolved call again and bound the xvalue as an lvalue:
// "invalid implicit conversion from 'struct str &' to 'struct str &&'"
// (std::vector<std::string> and std::operator+(const char *, string &&);
// CBMC's own c_preprocess.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
#include <initializer_list>
struct str
{
  int len;
  str(const char *s) : len(0)
  {
    while(s[len])
      ++len;
  }
  str(const str &o) = default;
  str(str &&o) : len(o.len)
  {
  }
};
// returns through an rvalue-reference parameter, as libstdc++'s
// operator+(const char *, basic_string &&) does
str operator+(const char *, str &&r)
{
  return str(static_cast<str &&>(r));
}
str name()
{
  return str("f.txt");
}
struct vec
{
  int n = 0, last = 0;
  vec(std::initializer_list<str> l)
  {
    for(const str &s : l)
    {
      ++n;
      last = s.len;
    }
  }
};
int run(const vec &v)
{
  return v.n * 10 + v.last;
}
int main()
{
  __CPROVER_assert(
    run({"cl", "@" + name()}) == 25, "resolved call among the elements");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
