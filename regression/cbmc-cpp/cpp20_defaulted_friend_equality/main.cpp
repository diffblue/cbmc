extern "C" void __CPROVER_assert(bool, const char *);
enum class errc
{
  ok = 0,
  bad = 1
};
struct to_chars_result
{
  char *ptr;
  errc ec;
  friend bool
  operator==(const to_chars_result &, const to_chars_result &) = default;
};
struct point
{
  int x, y;
  bool operator==(const point &) const = default;
};
// the member form over a padded layout (8-byte pointer, 4-byte int)
struct padded
{
  const char *name;
  int n;
  bool operator==(const padded &) const = default;
};
struct ordered
{
  long key;
  int tag;
  friend bool operator==(const ordered &, const ordered &) = default;
  friend bool operator!=(const ordered &, const ordered &) = default;
};
int main()
{
  char buf[4];
  to_chars_result a{buf, errc::ok}, b{buf, errc::ok}, c{buf + 1, errc::bad};
  __CPROVER_assert(a == b, "defaulted friend operator== compares the members");
  __CPROVER_assert(a != c, "and != is rewritten from it");
  point p{1, 2}, q{1, 3};
  __CPROVER_assert(p != q && p == p, "defaulted member operator==");
  padded r{"a", 1}, s{"a", 1}, t{"a", 2};
  __CPROVER_assert(r == s && !(r == t), "defaulted member == over padding");
  ordered u{5, 1}, v{5, 1}, w{5, 2};
  __CPROVER_assert(u == v && u != w, "defaulted friend == and != over padding");
  __CPROVER_assert(p == q, "WRONG (must FAIL)");
}
