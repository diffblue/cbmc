extern "C" void __CPROVER_assert(bool, const char *);
namespace lib
{
const char *find(const char *s, int c)
{
  while(*s != c)
    ++s;
  return s;
}
char *find(char *s, int c)
{
  return const_cast<char *>(find(static_cast<const char *>(s), c) + 1);
}
} // namespace lib
typedef const char *(*const_finder)(const char *, int);
typedef char *(*finder)(char *, int);
int main()
{
  // [over.over]/1.6, [expr.cast]: the target type of a C-style cast selects
  // the function of an overload set
  const_finder a = (const_finder)(lib::find);
  finder b = (finder)(&lib::find);
  char text[] = "abc";
  __CPROVER_assert(a(text, 'b') == text + 1, "const overload");
  __CPROVER_assert(b(text, 'b') == text + 2, "other overload");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
