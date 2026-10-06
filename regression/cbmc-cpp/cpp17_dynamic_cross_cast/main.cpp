// N5008 [expr.dynamic.cast]/5-6: dynamic_cast between UNRELATED
// polymorphic classes (a cross-cast) is well-formed; the run-time
// check yields a pointer to the target subobject when the most-derived
// object has one, and null otherwise.  CBMC rejected it outright
// ("type mismatch on dynamic_cast") because only the static up/down
// relationship was accepted -- the shape of libstdc++-free interface
// mixins and CBMC's own
//   dynamic_cast<hardness_collectort *>(&prop)
// (prop_conv_solver.h), which blocked 56 dog-food files.
//
// The result points to the iface_b subobject of the impl object
// ([expr.dynamic.cast]/9.2), so q->b() returns 2.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct iface_a
{
  virtual ~iface_a()
  {
  }
  virtual int a() = 0;
};

struct iface_b
{
  virtual ~iface_b()
  {
  }
  virtual int b() = 0;
};

struct impl : iface_a, iface_b
{
  int a() override
  {
    return 1;
  }
  int b() override
  {
    return 2;
  }
};

int probe(iface_a *p)
{
  iface_b *q = dynamic_cast<iface_b *>(p); // cross-cast
  if(q != nullptr)
    return q->b();
  return 0;
}

int main()
{
  impl obj;
  int r = probe(&obj);
  __CPROVER_assert(r == 2, "cross-cast to the sibling subobject");
  __CPROVER_assert(r == 0, "WRONG (must FAIL)");
  return 0;
}
