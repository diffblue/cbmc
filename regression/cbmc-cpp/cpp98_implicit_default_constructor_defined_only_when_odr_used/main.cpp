// N5008 [class.default.ctor]/4, [temp.inst]/3: zone's implicitly-declared
// default constructor is implicitly defined only when it is odr-used.  It
// is not, so holder<int>'s default constructor is not instantiated either,
// and neither is deleter<impl>::operator(), which would need the complete
// type impl.  Reduced from libstdc++ 13 <chrono> (std::chrono::time_zone's
// unique_ptr<_Impl>, test_chrono.desc).
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct deleter
{
  void operator()(T *p)
  {
    (void)sizeof(T);
    delete p;
  }
};

struct impl;

template <class T>
struct holder
{
  holder()
  {
    get_deleter()(0);
  }
  deleter<impl> get_deleter();
};

struct zone
{
  holder<int> h;
};

int main()
{
  zone *z = 0;
  __CPROVER_assert(z == 0, "no zone");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
