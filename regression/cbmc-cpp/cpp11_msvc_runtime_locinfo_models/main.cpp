// The shape of the MSVC STL's locale information (<xlocinfo>): _Locinfo's
// constructor and destructor and _Getcvt are defined in the runtime library
// (xlocinfo.cpp, wlocale.cpp), and so are the _X* functions that throw the
// standard exceptions (xthrow.cpp).  N5008 [locale.cons]/1, /4: the "C"
// locale is available; a locale name that is not makes std::locale throw
// runtime_error.
extern "C" void __CPROVER_assert(bool, const char *);
struct _Cvtvec
{
  unsigned int _Page;
  unsigned int _Mbcurmax;
  int _Isclocale;
  unsigned char _Isleadbyte[32];
};
extern "C" _Cvtvec __cdecl _Getcvt() noexcept;
namespace std
{
class runtime_error
{
public:
  explicit runtime_error(const char *_Message) : _What(_Message)
  {
  }
  const char *_What;
};
class length_error
{
public:
  explicit length_error(const char *_Message) : _What(_Message)
  {
  }
  const char *_What;
};
[[noreturn]] void __cdecl _Xruntime_error(const char *);
[[noreturn]] void __cdecl _Xlength_error(const char *);
template <class _Elem>
class _Yarn
{
public:
  _Yarn &operator=(const _Elem *_Right) noexcept
  {
    _Myptr = _Right;
    return *this;
  }
  const _Elem *_C_str() const noexcept
  {
    return _Myptr != nullptr ? _Myptr : &_Nul;
  }
  const _Elem *_Myptr = nullptr;
  _Elem _Nul = 0;
};
class _Locinfo
{
public:
  static void __cdecl _Locinfo_ctor(_Locinfo *, const char *);
  static void __cdecl _Locinfo_dtor(_Locinfo *);
  _Locinfo(const char *_Pch = "C")
  {
    if(_Pch)
    {
      _Locinfo_ctor(this, _Pch);
      return;
    }
    _Xruntime_error("bad locale name");
  }
  ~_Locinfo() noexcept
  {
    _Locinfo_dtor(this);
  }
  const char *_Getname() const
  {
    return _Newlocname._C_str();
  }
  _Yarn<char> _Oldlocname;
  _Yarn<char> _Newlocname;
};
} // namespace std

int main()
{
  {
    std::_Locinfo c;
    const char *n = c._Getname();
    __CPROVER_assert(n[0] == 'C' && n[1] == 0, "the C locale");
  }
  std::_Locinfo other("de_DE");
  const char *m = other._Getname();
  __CPROVER_assert(m[0] == '*' && m[1] == 0, "another locale is unavailable");
  _Cvtvec cvt = _Getcvt();
  __CPROVER_assert(
    cvt._Isclocale == 1 && cvt._Mbcurmax == 1 && cvt._Isleadbyte[0] == 0,
    "conversions of the C locale");
  bool thrown = false;
  try
  {
    std::_Xlength_error("too long");
  }
  catch(const std::length_error &e)
  {
    thrown = e._What[0] == 't';
  }
  __CPROVER_assert(thrown, "_Xlength_error throws length_error");
  __CPROVER_assert(!thrown, "WRONG (must FAIL)");
  return 0;
}
