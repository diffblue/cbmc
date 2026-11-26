extern "C" void __CPROVER_assert(bool, const char *);
struct buf
{
  int k = 5;
};
struct sbuf : buf
{
};
struct ios
{
  buf *b = nullptr;
};
// [over.match.ctor]/1, [over.match.viable]/2: for os(&s) only os(buf *) is
// viable -- os() takes no argument.  (libc++'s basic_ostringstream() :
// basic_ostream<_CharT, _Traits>(&__sb_), with basic_ostream's virtual base
// basic_ios.)
struct os : virtual ios
{
  explicit os(buf *p)
  {
    b = p;
  }

protected:
  os()
  {
  }
};
struct oss : os
{
  sbuf sb;
  oss() : os(&sb)
  {
  }
};
int main()
{
  sbuf s;
  os o(&s);
  __CPROVER_assert(o.b == &s, "direct initialization");
  oss d;
  __CPROVER_assert(d.b == &d.sb, "base initializer");
  __CPROVER_assert(o.b != &s, "WRONG (must FAIL)");
}
