// N5008 [expr.const]/5, [expr.add]/4: a constexpr function may initialize,
// assign and advance a pointer into a string literal (the shape of
// GCC 16's __unicode::__literal_encoding_is_unicode)
extern "C" void __CPROVER_assert(bool, const char *);
constexpr bool utf8(const char *enc)
{
  if(enc[0] == 'U' && enc[1] == 'T' && enc[2] == 'F')
  {
    enc += 3;
    if(enc[0] == '-')
      ++enc;
    return enc[0] == '8';
  }
  return false;
}
constexpr bool assigned()
{
  const char *e = "";
  e = "UTF-8";
  return utf8(e);
}
static_assert(utf8("UTF-8") && utf8("UTF8"), "advanced pointer");
static_assert(!utf8("ISO-8859-1"), "other encoding");
static_assert(assigned(), "assigned pointer");
template <unsigned U = utf8("UTF-8")>
int f()
{
  return int(U);
}
int main()
{
  __CPROVER_assert(f() == 1, "default template argument");
  __CPROVER_assert(f() == 0, "WRONG (must FAIL)");
  return 0;
}
