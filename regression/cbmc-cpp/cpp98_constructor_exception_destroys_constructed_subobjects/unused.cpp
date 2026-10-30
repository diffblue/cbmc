// N5008 [class.base.init]/13, [temp.inst]/3: the destructor of a subobject
// is potentially invoked by a constructor only if that constructor is
// defined; zone's implicit default constructor is not odr-used, so
// holder<impl>'s destructor, and the deleter for the incomplete impl, are
// not instantiated
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct deleter
{
  void operator()(T *p) const
  {
    char incomplete_check[sizeof(T) > 0 ? 1 : -1];
    (void)incomplete_check;
    delete p;
  }
};
template <class T>
struct holder
{
  T *p;
  ~holder()
  {
    deleter<T>()(p);
  }
};
struct impl;
struct zone
{
  int id;
  holder<impl> h;
  ~zone();
};
int main()
{
  zone *z = 0;
  __CPROVER_assert(z == 0, "no zone");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
