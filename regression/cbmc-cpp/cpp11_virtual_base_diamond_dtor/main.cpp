// Header-free replica of the iostream inheritance shape: a diamond
// whose top (iost) virtually inherits into istreamt/ostreamt, joined
// by iostreamt, with a further-derived streamt -- and the diamond top
// itself has a non-virtual base (ios_baset).  Destroying a streamt
// runs the full chain ([class.dtor]/13).  Guards the flat full-object
// pointer convention: make_ptr_typecast skips subobject-offset
// adjustment for virtually-inheriting hierarchies, so virtual-dispatch
// thunks must not subtract offsets either (they did, pushing `this`
// outside the object on every vtable-pointer write in the chain).
// Distilled from cpp11_stream_destructor_chain; fixed 2026-07-22.
// g++ and clang++ accept and the program verifies at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct ios_baset
{
  int b;
  virtual ~ios_baset()
  {
  }
};

struct iost : public ios_baset
{
  int m;
  virtual ~iost()
  {
  }
};

struct istreamt : virtual public iost
{
  int i;
  virtual ~istreamt()
  {
  }
};

struct ostreamt : virtual public iost
{
  int o;
  virtual ~ostreamt()
  {
  }
};

struct iostreamt : public istreamt, public ostreamt
{
  int io;
  virtual ~iostreamt()
  {
  }
};

struct streamt : public iostreamt
{
  int s;
  virtual ~streamt()
  {
  }
};

int main()
{
  {
    streamt ss;
  }
  int reached = 1;
  __CPROVER_assert(reached == 1, "destructor chain verifies");
  return 0;
}
