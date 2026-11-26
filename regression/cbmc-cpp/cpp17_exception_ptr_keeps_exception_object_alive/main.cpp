// N5008 [except.throw]/4: the exception object is destroyed at the last of
// its points of potential destruction: when its last active handler exits,
// or when the last std::exception_ptr that refers to it is destroyed
// ([propagation]/7).  current_exception() refers to it ([propagation]/9),
// copies of an exception_ptr compare equal, and rethrow_exception throws
// the same object again ([propagation]/10).
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);

int destroyed = 0;
struct E
{
  int v;
  explicit E(int x) : v(x)
  {
  }
  E(const E &o) : v(o.v)
  {
  }
  ~E()
  {
    ++destroyed;
  }
};

std::exception_ptr capture(int v)
{
  try
  {
    throw E(v);
  }
  catch(const E &)
  {
    return std::current_exception();
  }
}

int main()
{
  std::exception_ptr none;
  __CPROVER_assert(!none, "default exception_ptr is null");
  {
    std::exception_ptr p = capture(7);
    __CPROVER_assert(destroyed == 0, "kept alive by an exception_ptr");
    __CPROVER_assert(p != none, "refers to the exception");
    std::exception_ptr q = p;
    __CPROVER_assert(q == p, "copies are equal");
    p = nullptr;
    __CPROVER_assert(destroyed == 0, "kept alive by the copy");
  }
  __CPROVER_assert(destroyed == 1, "destroyed with the last exception_ptr");

  std::exception_ptr r = capture(5);
  int seen = 0;
  for(int i = 0; i < 2; ++i)
  {
    try
    {
      std::rethrow_exception(r);
    }
    catch(const E &e)
    {
      seen += e.v;
    }
  }
  __CPROVER_assert(seen == 10, "rethrown twice");
  __CPROVER_assert(destroyed == 1, "still referred to");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
