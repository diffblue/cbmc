// N5008 [except.throw]/8: a `throw;` with no operand rethrows the exception
// currently being handled -- the exception of the (dynamically) enclosing
// handler.  Complements cpp11_throw_rethrow_nested: here the rethrow is in the
// INNER handler, so it must re-propagate the INNER exception E(2) -- not the
// outer E(1) the enclosing handler is handling.  This guards against a fix that
// keys the "exception being handled" too coarsely (e.g. always the outermost).

extern "C" void __CPROVER_assert(int, const char *);

struct E
{
  int c;
  E(int x) : c(x)
  {
  }
};

int main()
{
  int reached = 0;
  try
  {
    try
    {
      throw E(1);
    }
    catch(E &outer)
    {
      try
      {
        throw E(2);
      }
      catch(E &inner)
      {
        throw; // must rethrow E(2), the exception the inner handler handles
      }
    }
  }
  catch(E &e)
  {
    reached = 1;
    __CPROVER_assert(reached == 1, "outer handler reached after inner rethrow");
    __CPROVER_assert(
      e.c == 2, "inner rethrow re-propagates the inner exception E(2)");
  }
  return 0;
}
