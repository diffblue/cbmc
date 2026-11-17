// The shape of the MSVC STL's ctype data (<xlocinfo>): _Getctype and
// _Mbrtowc are defined in the runtime library (xlocinfo.cpp, xmbtowc.cpp).
// N5008 [facet.ctype.char.statics]/1: the table classifies the characters
// of the "C" locale; [c.mb.wcs]/4 (C17 7.29.6.3.2): in the "C" locale a
// byte converts to the wide character of the same value.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C"
{
  typedef decltype(sizeof 0) size_t;
  typedef struct _Mbstatet
  {
    unsigned long _Wchar;
    unsigned short _Byte, _State;
  } _Mbstatet;
  typedef _Mbstatet mbstate_t;
  struct _Ctypevec
  {
    unsigned int _Page;
    const short *_Table;
    int _Delfl;
    wchar_t *_LocaleName;
  };
  struct _Cvtvec
  {
    unsigned int _Page;
    unsigned int _Mbcurmax;
    int _Isclocale;
    unsigned char _Isleadbyte[32];
  };
  _Ctypevec __cdecl _Getctype() noexcept;
  _Cvtvec __cdecl _Getcvt() noexcept;
  int __cdecl _Mbrtowc(
    wchar_t *,
    const char *,
    size_t _Max_multibyte,
    mbstate_t *,
    const _Cvtvec *) noexcept;
}

int main()
{
  _Ctypevec ct = _Getctype();
  const short *t = ct._Table;
  // the masks of the MSVC STL's ctype_base: upper 0x1, lower 0x2, digit
  // 0x4, space 0x8 | 0x40, punct 0x10, cntrl 0x20, xdigit 0x80
  __CPROVER_assert(
    (t['A'] & 0x1) && (t['z'] & 0x2) && (t['7'] & 0x4) && (t['7'] & 0x80) &&
      (t[' '] & 0x8) && (t['\n'] & 0x8) && (t['!'] & 0x10) &&
      (t['\t'] & 0x20) && !(t['g'] & 0x80) && t[200] == 0 && ct._Delfl == 0 &&
      ct._LocaleName == nullptr,
    "classification of the C locale");
  _Cvtvec cvt = _Getcvt();
  mbstate_t st{};
  wchar_t wc = 0;
  int n = _Mbrtowc(&wc, "x", 1, &st, &cvt);
  __CPROVER_assert(n == 1 && wc == L'x', "one byte, one character");
  __CPROVER_assert(
    _Mbrtowc(&wc, "", 1, &st, &cvt) == 0 && wc == 0, "the null character");
  __CPROVER_assert(n == 0, "WRONG (must FAIL)");
  return 0;
}
