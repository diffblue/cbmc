// N5008 [class.base.init]/7 and /13: a mem-initializer may name an INDIRECT
// virtual base, and it is the most derived class's constructor that
// initializes the virtual base -- the intermediate classes' initializers
// for it are ignored.  Destruction is the reverse: the most derived class
// destroys the virtual base once, after its direct bases ([class.dtor]/14).
extern "C" void __CPROVER_assert(bool, const char *);
int v_ctor, v_dtor, log_[8], log_n;
struct V
{
  int v;
  explicit V(int x) : v(x)
  {
    v_ctor++;
  }
  ~V()
  {
    v_dtor++;
    log_[log_n++] = 1;
  }
};
struct B1 : virtual V
{
  int b1;
  B1() : V(100), b1(1)
  {
  }
  ~B1()
  {
    log_[log_n++] = 2;
  }
};
struct B2 : virtual V
{
  int b2;
  B2() : V(200), b2(2)
  {
  }
  ~B2()
  {
    log_[log_n++] = 3;
  }
};
struct D : B1, B2
{
  int d;
  D() : V(7), d(3)
  {
  }
  ~D()
  {
    log_[log_n++] = 4;
  }
};
int main()
{
  {
    D o;
    __CPROVER_assert(v_ctor == 1, "V constructed once");
    __CPROVER_assert(o.v == 7, "the most derived class's initializer wins");
    __CPROVER_assert(o.b1 == 1 && o.b2 == 2 && o.d == 3, "members");
    B2 *p = &o;
    __CPROVER_assert(p->v == 7 && p->b2 == 2, "through B2*");
  }
  __CPROVER_assert(v_dtor == 1, "V destroyed once");
  __CPROVER_assert(
    log_n == 4 && log_[0] == 4 && log_[1] == 3 && log_[2] == 2 && log_[3] == 1,
    "destruction order: D, B2, B1, then the virtual base V");
  {
    B1 b;
    __CPROVER_assert(b.v == 100, "as a complete object, B1 initializes V");
  }
  __CPROVER_assert(v_ctor == 2 && v_dtor == 2, "complete B1 owns its V");
  return 0;
}
