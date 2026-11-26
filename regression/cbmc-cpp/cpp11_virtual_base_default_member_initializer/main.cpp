// N5008 [class.base.init]/9.1, [class.default.ctor]/4: a virtual base that
// is not named in a mem-initializer-list is default-initialized by the
// most derived class, which applies its default member initializers
extern "C" void __CPROVER_assert(bool, const char *);
struct ios
{
  int q = 5;
  const int *p = nullptr;
  int fill() const
  {
    return 3;
  }
};
// libstdc++'s basic_ostream : virtual basic_ios
struct ostream : virtual ios
{
  int last = 0;
  int insert(long v)
  {
    last = (this->p == nullptr ? 1 : 2) + this->fill() + (int)v;
    return last;
  }
};
struct with_ctor : virtual ios
{
  int r;
  with_ctor() : r(q)
  {
  }
};
// the most derived class initializes the shared virtual base once
struct left : virtual ios
{
};
ios seven()
{
  ios i;
  i.q = 7;
  return i;
}
// [class.base.init]/7: this mem-initializer is ignored in a diamond
struct right : virtual ios
{
  right() : ios(seven())
  {
  }
};
struct diamond : left, right
{
  int q = 9; // hides ios::q
};
int main()
{
  ostream o;
  __CPROVER_assert(o.q == 5 && o.p == nullptr, "implicit constructor");
  __CPROVER_assert(o.insert(4) == 8, "member function reads them");
  with_ctor w;
  __CPROVER_assert(w.r == 5, "user-provided constructor");
  diamond d;
  __CPROVER_assert(d.ios::q == 5, "most derived class initializes it");
  __CPROVER_assert(d.q == 9, "hiding member");
  right r;
  __CPROVER_assert(r.q == 7, "its own mem-initializer");
  __CPROVER_assert(o.q != 5, "WRONG (must FAIL)");
}
