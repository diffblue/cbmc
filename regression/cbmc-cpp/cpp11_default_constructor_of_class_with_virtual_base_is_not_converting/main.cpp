// N5008 [class.conv.ctor]/1: a converting constructor is one that is not
// explicit and can be called with one argument.  The front end adds a
// hidden `@most_derived' parameter to the constructors of a class with
// virtual bases; the DEFAULT constructor then looked like a converting
// constructor from bool, so `std::istringstream in("text")' was ambiguous
// between istringstream(const string &) and istringstream(istringstream &&)
// -- the latter "converting" the char array to bool (CBMC's own
// c_preprocess.cpp, dog-fooding).  Modelled here without the library.
extern "C" void __CPROVER_assert(bool, const char *);
struct str
{
  int n;
  str(const char *s) : n(0)
  {
    while(s[n])
      ++n;
  }
};
struct ios
{
  int flags = 0;
  virtual ~ios()
  {
  }
};
struct istream : virtual ios
{
  int st = 0;
};
struct stream : istream
{
  int len;
  int kind;
  stream() : len(-1), kind(0)
  {
  }
  explicit stream(const str &s, int mode = 0) : len(s.n), kind(1)
  {
  }
  stream(stream &&o) : len(o.len), kind(2)
  {
  }
};
int main()
{
  stream in("hello world");
  __CPROVER_assert(
    in.len == 11 && in.kind == 1,
    "const char[12] converts to str, not to a stream");
  stream d;
  __CPROVER_assert(d.kind == 0 && d.len == -1, "default constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
