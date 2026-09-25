// N5008 [class.conv.fct]/2: an explicit conversion function is only
// considered as a user-defined conversion for direct-initialization.  Every
// conversion function was taken as implicit, so for `CIt(loc)' -- loc with
// `explicit operator It()' and `explicit operator CIt()' -- BOTH
// constructors `CIt(const CIt &)' and `CIt(const It &)' were viable ("does
// not uniquely resolve"; libstdc++ 16's `const_iterator(__loc)' on
// _Hashtable::__location_type, which dropped find()).  Per
// [over.match.copy]/1.2 the direct-initialization `T(x)' admits an explicit
// conversion function yielding T for the copy constructor's `T&' parameter;
// per [conv.general]/4 the contextual conversion to bool (if, while, !, &&,
// ?:) and per [over.match.conv]/1 the direct-initialization of a non-class
// object (`bool b(x)', `static_cast<int>(x)') admit explicit ones too.
extern "C" void __CPROVER_assert(bool, const char *);
struct It
{
  int v;
};
struct CIt
{
  int v;
  CIt() : v(0)
  {
  }
  explicit CIt(int p) : v(p)
  {
  }
  CIt(const It &x) : v(x.v + 100)
  {
  }
};
struct Loc
{
  int n;
  explicit operator bool() const
  {
    return n != 0;
  }
  explicit operator It() const
  {
    return It{n};
  }
  explicit operator CIt() const
  {
    return CIt(n);
  }
  explicit operator int() const
  {
    return n * 10;
  }
};
Loc mk(int n)
{
  return Loc{n};
}
int contextual(int n)
{
  int r = 0;
  if(auto loc = mk(n))
    r += 1;
  if(mk(n))
    r += 2;
  if(!mk(n))
    r += 4;
  r += mk(n) ? 8 : 0;
  r += (mk(n) && true) ? 16 : 0;
  while(mk(n))
  {
    r += 32;
    break;
  }
  bool b(mk(n));
  r += b ? 64 : 0;
  r += static_cast<int>(mk(n));
  return r;
}
int main()
{
  Loc loc{7};
  __CPROVER_assert(CIt(loc).v == 7, "T(x): explicit operator T() selected");
  __CPROVER_assert(It(loc).v == 7, "aggregate T(x) via explicit operator T()");
  __CPROVER_assert(static_cast<CIt>(loc).v == 7, "static_cast<T>(x)");
  __CPROVER_assert(
    contextual(1) == 1 + 2 + 8 + 16 + 32 + 64 + 10,
    "contextual and direct-initialization");
  __CPROVER_assert(contextual(0) == 4, "false");
  __CPROVER_assert(CIt(loc).v == 107, "WRONG (must FAIL)");
}
