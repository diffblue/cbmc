extern "C" void __CPROVER_assert(bool, const char *);
int log_[16], n;
struct V
{
  int v;
  V() : v(5)
  {
  }
  virtual int g()
  {
    return 10;
  }
  virtual ~V()
  {
  }
};
struct M : virtual V
{
  int g() override
  {
    return 20;
  }
  M()
  {
    V *pv = this; // through the virtual base's pointer as well
    log_[n++] = pv->g();
    log_[n++] = v; // the virtual base is constructed already
  }
  ~M() override
  {
    V *pv = this;
    log_[n++] = pv->g();
  }
};
struct N : virtual V
{
  int g() override
  {
    return 25;
  }
  N()
  {
    log_[n++] = g();
  }
  ~N() override
  {
    log_[n++] = g();
  }
};
struct E : M, N
{
  int g() override
  {
    return 30;
  }
  E()
  {
    log_[n++] = g();
  }
  ~E() override
  {
    log_[n++] = g();
  }
};
int main()
{
  {
    E e;
    __CPROVER_assert(e.g() == 30 && static_cast<V &>(e).g() == 30, "complete");
  }
  __CPROVER_assert(n == 7, "seven calls");
  __CPROVER_assert(
    log_[0] == 20 && log_[1] == 5, "M's constructor sees M::g through V*");
  __CPROVER_assert(log_[2] == 25, "N's constructor sees N::g");
  __CPROVER_assert(log_[3] == 30, "E's constructor sees E::g");
  __CPROVER_assert(
    log_[4] == 30 && log_[5] == 25 && log_[6] == 20, "destruction: E, N, M");
  return 0;
}
