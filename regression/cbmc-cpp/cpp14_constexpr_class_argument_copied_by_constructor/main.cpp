// N5008 [expr.call]/7, [class.copy.ctor]/12, /14, [expr.const]/9: a
// constexpr object passed by value to a constexpr function is copied by the
// class's copy constructor -- implicit, or defaulted -- whose value is that
// of the source; a member function called on the copy reads its members.
// libc++'s and libstdc++'s string_view comparisons pass views this way.
extern "C" void __CPROVER_assert(bool, const char *);

struct V
{
  const char *p;
  unsigned long n;
  constexpr V(const char *s, unsigned long k) : p(s), n(k)
  {
  }
  constexpr const char *data() const
  {
    return p;
  }
};

struct W
{
  const char *p;
  constexpr W(const char *s) : p(s)
  {
  }
  constexpr W(const W &) = default;
  constexpr char first() const
  {
    return p[0];
  }
};

constexpr char first(V v)
{
  return v.data()[0];
}
constexpr char second(V v)
{
  return v.p[1];
}
constexpr char first_w(W w)
{
  return w.first();
}

int main()
{
  constexpr V a("32", 2);
  static_assert(first(a) == '3', "implicit copy, member function");
  static_assert(second(a) == '2', "implicit copy, member");
  constexpr W b("xy");
  static_assert(first_w(b) == 'x', "defaulted copy");
  __CPROVER_assert(first(a) == '3' && first_w(b) == 'x', "run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
