// N5008 [class.virtual]/2, /7: a virtual call invokes the final overrider
// in the dynamic type of the object, which is a class having the function
// as a member; a function of an unrelated class with the same signature
// is never called
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" int nondet_int();
struct facet
{
  virtual ~facet()
  {
  }
};
struct numpunct : facet
{
  int f() const
  {
    return do_f();
  }
  virtual int do_f() const
  {
    return 1;
  }
};
struct derived : numpunct
{
  int do_f() const
  {
    return 4;
  }
};
struct unrelated : facet
{
  virtual int do_g() const
  {
    return 2;
  }
};
int main()
{
  numpunct n;
  derived d;
  unrelated u;
  facet *table[3] = {&n, &d, &u};
  int i = nondet_int();
  if(i < 0 || i > 1)
    i = 0;
  const numpunct *p = static_cast<const numpunct *>(table[i]);
  int r = p->f();
  __CPROVER_assert(r == 1 || r == 4, "final overrider");
  __CPROVER_assert(r == 1, "WRONG (must FAIL)");
  return 0;
}
