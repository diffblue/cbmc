// N5008 [std.manip]/2-6: setw, setprecision, setbase, setiosflags and
// resetiosflags return an object that, inserted into or extracted from a
// stream, sets its field width, precision, base or flags.  The shape of the
// MSVC STL (<iomanip>): they return an _Smanip holding a function pointer
// and are defined in the runtime library (iomanip.cpp), so the headers only
// declare them.
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
typedef long long streamsize;
class ios_base
{
public:
  typedef int fmtflags;
  static constexpr fmtflags dec = 0x200, oct = 0x400, hex = 0x800,
                            basefield = 0xe00, showpos = 0x20;
  fmtflags flags() const
  {
    return _Fmtfl;
  }
  fmtflags setf(fmtflags _Newfmtflags)
  {
    fmtflags _Oldfmtflags = _Fmtfl;
    _Fmtfl |= _Newfmtflags;
    return _Oldfmtflags;
  }
  fmtflags setf(fmtflags _Newfmtflags, fmtflags _Mask)
  {
    fmtflags _Oldfmtflags = _Fmtfl;
    _Fmtfl = (_Fmtfl & ~_Mask) | (_Newfmtflags & _Mask);
    return _Oldfmtflags;
  }
  streamsize precision(streamsize _Newprecision)
  {
    streamsize _Oldprecision = _Prec;
    _Prec = _Newprecision;
    return _Oldprecision;
  }
  streamsize precision() const
  {
    return _Prec;
  }
  streamsize width(streamsize _Newwidth)
  {
    streamsize _Oldwidth = _Wide;
    _Wide = _Newwidth;
    return _Oldwidth;
  }
  streamsize width() const
  {
    return _Wide;
  }
  fmtflags _Fmtfl = dec;
  streamsize _Prec = 6;
  streamsize _Wide = 0;
};
template <class _Arg>
struct _Smanip
{
  _Smanip(void(__cdecl *_Left)(ios_base &, _Arg), _Arg _Val)
    : _Pfun(_Left), _Manarg(_Val)
  {
  }
  void apply(ios_base &_Iostr) const
  {
    (*_Pfun)(_Iostr, _Manarg);
  }
  void(__cdecl *_Pfun)(ios_base &, _Arg);
  _Arg _Manarg;
};
_Smanip<ios_base::fmtflags> __cdecl resetiosflags(ios_base::fmtflags);
_Smanip<ios_base::fmtflags> __cdecl setiosflags(ios_base::fmtflags);
_Smanip<int> __cdecl setbase(int);
_Smanip<streamsize> __cdecl setprecision(streamsize);
_Smanip<streamsize> __cdecl setw(streamsize);
} // namespace std

int main()
{
  std::ios_base s;
  std::setw(4).apply(s);
  __CPROVER_assert(s.width() == 4, "setw");
  std::setprecision(3).apply(s);
  __CPROVER_assert(s.precision() == 3, "setprecision");
  std::setbase(16).apply(s);
  __CPROVER_assert(
    (s.flags() & std::ios_base::basefield) == std::ios_base::hex, "setbase");
  std::setiosflags(std::ios_base::showpos).apply(s);
  __CPROVER_assert((s.flags() & std::ios_base::showpos) != 0, "setiosflags");
  std::resetiosflags(std::ios_base::showpos).apply(s);
  __CPROVER_assert((s.flags() & std::ios_base::showpos) == 0, "resetiosflags");
  __CPROVER_assert(s.width() == 0, "WRONG (must FAIL)");
  return 0;
}
