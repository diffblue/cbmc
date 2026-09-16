extern "C" void __CPROVER_assert(bool, const char *);
template <class _CharT>
struct It
{
  static int w() { return sizeof(_CharT); }
};
// default given on the FORWARD declaration ([temp.param]/12), as in
// libstdc++'s <bits/localefwd.h>; the DEFINITION follows later, after
// the enclosing template below (so its parameter scope is numbered
// after numpunct's)
template <class _CharT, class _InIter = It<_CharT>>
struct num_get;
// enclosing template whose own parameter is ALSO called _CharT and
// bound to char while num_get<wchar_t> is named (the
// _GLIBCXX_STD_FACET table shape in __try_use_facet)
template <class C, class D>
struct second
{
  typedef D type;
};
template <class _CharT>
struct numpunct
{
  static int probe()
  {
    // dependent spellings so the uses are valid before num_get is complete
    int a = num_get<typename second<_CharT, char>::type>::w();
    int b = num_get<typename second<_CharT, wchar_t>::type>::w();
    int c = num_get<typename second<_CharT, short>::type>::w();
    return a * 100 + b * 10 + c;
  }
};
template <class _CharT, class _InIter>
struct num_get
{
  static int w() { return _InIter::w(); }
};
int main()
{
  __CPROVER_assert(numpunct<char>::probe() == 100 + 40 + 2, "defaults bind the named template's own _CharT");
  __CPROVER_assert(numpunct<wchar_t>::probe() == 100 + 40 + 2, "again from a wchar_t context");
  return 0;
}
