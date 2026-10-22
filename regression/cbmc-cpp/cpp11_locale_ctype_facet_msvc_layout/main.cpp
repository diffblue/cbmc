// N5008 [locale.cons]/1, [locale.general]/8, [facet.ctype.special]: the
// default locale is the "C" locale, whose ctype<char> classifies as in the
// C library.  The shape of the MSVC STL: the classification table is
// ctype<char>::_Ctype._Table, the masks are enumerators of ctype_base, and
// locale::_Init and _Lockit are defined in the runtime library.
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
struct _Lockit
{
  explicit _Lockit(int);
  ~_Lockit();
};
struct _Ctypevec
{
  unsigned int _Page;
  const short *_Table;
};
struct ctype_base
{
  enum
  {
    alnum = 0x4 | 0x2 | 0x1 | 0x100,
    alpha = 0x2 | 0x1 | 0x100,
    cntrl = 0x20,
    digit = 0x4,
    graph = 0x4 | 0x2 | 0x10 | 0x1 | 0x100,
    lower = 0x2,
    print = 0x4 | 0x2 | 0x10 | 0x40 | 0x1 | 0x100 | 0x80,
    punct = 0x10,
    space = 0x8 | 0x40,
    upper = 0x1,
    xdigit = 0x80,
    blank = 0x8 | 0x40
  };
  typedef short mask;
};
class locale
{
public:
  class facet
  {
  public:
    void _Incref() noexcept
    {
      ++_Myrefs;
    }
    facet *_Decref() noexcept
    {
      return --_Myrefs == 0 ? this : nullptr;
    }

  protected:
    explicit facet(unsigned long refs = 0) noexcept : _Myrefs(refs)
    {
    }

  private:
    unsigned long _Myrefs;
  };
  class _Locimp : public facet
  {
  public:
    explicit _Locimp(bool) : facet(1)
    {
    }
  };
  locale() noexcept : _Ptr(_Init(true))
  {
  }
  ~locale() noexcept
  {
    if(_Ptr)
      _Ptr->_Decref();
  }
  _Locimp *_Ptr;
  static _Locimp *_Init(bool _Do_incref = false);
};
template <class>
class ctype;
template <>
class ctype<char> : public ctype_base
{
public:
  bool is(mask m, char c) const
  {
    return (_Ctype._Table[static_cast<unsigned char>(c)] & m) != 0;
  }
  _Ctypevec _Ctype;
};
template <class F>
const F &use_facet(const locale &l)
{
  _Lockit lock(0);
  return *reinterpret_cast<const F *>(l._Ptr);
}
} // namespace std
int main()
{
  std::locale loc;
  const std::ctype<char> &ct = std::use_facet<std::ctype<char>>(loc);
  __CPROVER_assert(ct.is(std::ctype_base::digit, '5'), "5 is a digit");
  __CPROVER_assert(!ct.is(std::ctype_base::digit, 'a'), "a is not a digit");
  __CPROVER_assert(ct.is(std::ctype_base::alpha, 'a'), "a is alpha");
  __CPROVER_assert(ct.is(std::ctype_base::space, '\n'), "newline is space");
  __CPROVER_assert(!ct.is(std::ctype_base::upper, 'z'), "z is not upper");
  __CPROVER_assert(ct.is(std::ctype_base::punct, ','), "comma is punct");
  __CPROVER_assert(ct.is(std::ctype_base::upper, 'a'), "WRONG (must FAIL)");
  return 0;
}
