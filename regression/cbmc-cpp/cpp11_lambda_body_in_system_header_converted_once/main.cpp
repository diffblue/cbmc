extern "C" void __CPROVER_assert(bool, const char *);
// the class comes from a "system header" (as libc++'s basic_string does):
// the front end completes half-converted system-header bodies in an
// end-of-unit sweep, which must not re-convert a lambda's body
#line 1 "/usr/include/c++/fake/string.h"
struct pair
{
  int first;
  int second;
};
pair &&mv(pair &p)
{
  return static_cast<pair &&>(p);
}
struct string
{
  pair r_;
  string(int a, int b) : r_{a, b}
  {
  }
  // libc++ 18's basic_string(basic_string &&): the member is initialized
  // through an immediately-invoked lambda whose trailing return type names
  // the member and whose body returns the xvalue of a call to std::move
  string(string &&s)
    : r_([](string &o) -> decltype(r_) && { return mv(o.r_); }(s))
  {
    s.r_.first = 0;
    s.r_.second = 0;
  }
  int size() const
  {
    return r_.first;
  }
};
#line 33 "main.cpp"
int main()
{
  string a(3, 7);
  string b(static_cast<string &&>(a));
  __CPROVER_assert(b.size() == 3, "moved string keeps its size");
  __CPROVER_assert(b.r_.second == 7, "and its second member");
  __CPROVER_assert(a.size() == 0, "the moved-from object is reset");
  __CPROVER_assert(b.size() == 4, "WRONG (must FAIL)");
}
