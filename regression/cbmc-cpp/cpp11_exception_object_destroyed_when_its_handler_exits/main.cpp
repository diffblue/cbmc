// N5008 [except.throw]/5: the exception object is destroyed when the last
// active handler for it exits by any means other than rethrowing: at the
// end of its block, by a return, or by another exception leaving it.
// [except.handle]/15: a handler parameter of reference type refers to the
// exception object.
extern "C" void __CPROVER_assert(bool, const char *);

int live = 0;

struct E
{
  int v = 1;
  E()
  {
    ++live;
  }
  E(const E &o) : v(o.v)
  {
    ++live;
  }
  ~E()
  {
    --live;
  }
};
struct F
{
  F()
  {
    ++live;
  }
  F(const F &)
  {
    ++live;
  }
  ~F()
  {
    --live;
  }
};

int from_return()
{
  try
  {
    throw E();
  }
  catch(const E &)
  {
    return 1;
  }
  return 0;
}

int main()
{
  __CPROVER_assert(from_return() == 1 && live == 0, "left by return");
  try
  {
    try
    {
      throw E();
    }
    catch(const E &)
    {
      throw F();
    }
  }
  catch(const F &)
  {
    __CPROVER_assert(live == 1, "E destroyed when F leaves its handler");
  }
  __CPROVER_assert(live == 0, "F destroyed after its handler");
  try
  {
    throw E();
  }
  catch(...)
  {
  }
  __CPROVER_assert(live == 0, "catch(...)");
  int seen = 0;
  try
  {
    throw E();
  }
  catch(E &e)
  {
    e.v = 5;
    try
    {
      throw;
    }
    catch(const E &again)
    {
      seen = again.v;
    }
  }
  __CPROVER_assert(seen == 5, "reference to the exception object");
  __CPROVER_assert(live == 0, "rethrown and destroyed once");
  __CPROVER_assert(live == 1, "WRONG (must FAIL)");
  return 0;
}
