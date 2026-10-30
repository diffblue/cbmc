// N5008 [expr.const], [dcl.constexpr]/3 (C++14: loops and assignments in a
// constexpr function): a constexpr function may walk a string literal through
// a pointer -- [expr.add]/4 pointer arithmetic, [expr.unary.op]/1 `*p',
// [expr.post.incr]/[expr.pre.incr] `p++'/`++p'.  The constant evaluator
// tracked the pointer as `&"abc"[0]' but could not move it, and -- worse --
// a statement whose effect it could not apply was skipped while evaluation
// CONTINUED with stale values: `++p; return *p' returned the character
// BEFORE the increment, and `while(*p++) ++n' returned 0, so
// `static_assert(len("abc") == 3)' FAILED (a wrong verdict).  Now pointers
// into string literals are tracked with their index, and an effect that
// cannot be tracked abandons the evaluation instead of corrupting it.
extern "C" void __CPROVER_assert(bool, const char *);

constexpr int len(const char *p)
{
  int n = 0;
  while(*p++)
    ++n;
  return n;
}
constexpr int len2(const char *p)
{
  int n = 0;
  while(p[n])
    ++n;
  return n;
}
constexpr int deref_inc(const char *p)
{
  ++p;
  return *p;
}
constexpr int post_inc(const char *p)
{
  return *p++;
}
constexpr int skip(const char *p, int k)
{
  p += k;
  return *p;
}
constexpr int last(const char *p)
{
  const char *q = p;
  while(*q)
    ++q;
  --q;
  return *q;
}
constexpr const char *s = "hello";

static_assert(len("abc") == 3, "len");
static_assert(len(s) == 5, "len via constexpr pointer");
static_assert(len2("abcd") == 4, "len2");
static_assert(deref_inc("abc") == 'b', "++p; *p");
static_assert(post_inc("abc") == 'a', "*p++");
static_assert(skip("abcdef", 4) == 'e', "p += k");
static_assert(last("xyz") == 'z', "walk to the end and back");
static_assert(len("") == 0, "empty");

int main()
{
  constexpr int n = len("four");
  static_assert(n == 4, "block scope");
  int r = n;
  __CPROVER_assert(r == 4, "folded value at run time");
  __CPROVER_assert(r == 5, "WRONG (must FAIL)");
}
