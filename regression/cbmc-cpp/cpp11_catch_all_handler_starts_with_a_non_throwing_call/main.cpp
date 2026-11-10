// N5008 [except.handle]/9: a handler is active once entered, so the
// exception is no longer in flight while its statements run; a
// non-throwing function called first in a catch(...) handler returns
// normally ([except.terminate]/1.3 does not apply).
extern "C" void __CPROVER_assert(bool, const char *);
int calls = 0;
void f() noexcept
{
  ++calls;
}
int main()
{
  try
  {
    throw 1;
  }
  catch(...)
  {
    f();
  }
  __CPROVER_assert(calls == 1, "handler completes");
  __CPROVER_assert(calls == 0, "WRONG (must FAIL)");
  return 0;
}
