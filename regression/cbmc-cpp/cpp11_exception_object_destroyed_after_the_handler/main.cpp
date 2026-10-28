// N5008 [except.throw]/5: the exception object is destroyed when the last
// active handler for it exits other than by rethrowing (and no
// exception_ptr refers to it).  With a handler of reference type there is
// no parameter object; e and the exception object are each constructed
// once and destroyed once, also when the exception is rethrown
// ([expr.throw]/3: no new exception object is created).
extern "C" void __CPROVER_assert(bool, const char *);

int constructed = 0;
int destroyed[4] = {0, 0, 0, 0};

struct E
{
  int id;
  E() : id(constructed++)
  {
  }
  E(const E &) : id(constructed++)
  {
  }
  ~E()
  {
    if(id >= 0 && id < 4)
      ++destroyed[id];
  }
};

int main()
{
  {
    E e;
    try
    {
      try
      {
        throw e;
      }
      catch(const E &x)
      {
        __CPROVER_assert(x.id != e.id, "the exception object is a copy");
        throw;
      }
    }
    catch(const E &y)
    {
      __CPROVER_assert(y.id == 1, "the rethrown exception is the same object");
    }
  }
  __CPROVER_assert(constructed == 2, "e and the exception object");
  bool once = true;
  for(int i = 0; i < constructed && i < 4; ++i)
    once = once && destroyed[i] == 1;
  __CPROVER_assert(once, "each object destroyed exactly once");
  __CPROVER_assert(!once, "WRONG (must FAIL)");
  return 0;
}
