// N5008 [locale.cons]/1, /5, /9, [locale.general]/8: default-constructed
// and copied locales denote the global locale, the "C" locale; destroying
// them leaves it usable.  The shape of the MSVC STL: locale::_Init and
// _Getgloballocale, defined in the runtime library, yield the global
// implementation object, whose facets are reference counted with
// _InterlockedIncrement / _InterlockedDecrement, and ~locale deletes the
// result of _Decref, which is null while references remain.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" long _InterlockedIncrement(long volatile *);
extern "C" long _InterlockedDecrement(long volatile *);
namespace std
{
struct _Facet_base
{
  virtual ~_Facet_base() noexcept
  {
  }
  virtual void _Incref() noexcept = 0;
  virtual _Facet_base *_Decref() noexcept = 0;
};
class locale
{
public:
  class facet : public _Facet_base
  {
  public:
    void _Incref() noexcept override
    {
      _InterlockedIncrement(&_Myrefs);
    }
    _Facet_base *_Decref() noexcept override
    {
      return _InterlockedDecrement(&_Myrefs) == 0 ? this : nullptr;
    }

  protected:
    explicit facet(unsigned long refs = 0) noexcept : _Myrefs(long(refs))
    {
    }

  private:
    long _Myrefs;
  };
  class _Locimp : public facet
  {
  public:
    explicit _Locimp(bool transparent)
      : facet(1), _Facetvec(nullptr), _Facetcount(0), _Xparent(transparent)
    {
    }
    facet **_Facetvec;
    unsigned long _Facetcount;
    bool _Xparent;
  };
  locale() noexcept : _Ptr(_Init(true))
  {
  }
  locale(const locale &other) noexcept : _Ptr(other._Ptr)
  {
    _Ptr->_Incref();
  }
  ~locale() noexcept
  {
    if(_Ptr)
      delete _Ptr->_Decref();
  }
  const facet *_Getfacet(unsigned long id) const
  {
    const facet *f = id < _Ptr->_Facetcount ? _Ptr->_Facetvec[id] : nullptr;
    if(f || !_Ptr->_Xparent)
      return f;
    _Locimp *global = _Getgloballocale();
    return id < global->_Facetcount ? global->_Facetvec[id] : nullptr;
  }
  _Locimp *_Ptr;
  static _Locimp *_Init(bool _Do_incref = false);
  static _Locimp *_Getgloballocale();
};
} // namespace std
int main()
{
  {
    std::locale a;
    std::locale b(a);
    __CPROVER_assert(a._Ptr == b._Ptr, "copies share the implementation");
  }
  std::locale c;
  __CPROVER_assert(c._Getfacet(3) == nullptr, "no facets of its own");
  __CPROVER_assert(
    c._Ptr == std::locale::_Getgloballocale(), "the global locale");
  __CPROVER_assert(c._Ptr == nullptr, "WRONG (must FAIL)");
  return 0;
}
