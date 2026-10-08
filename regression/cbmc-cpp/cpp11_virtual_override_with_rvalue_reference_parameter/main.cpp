// N5008 [class.virtual]/14, [expr.prim.id.unqual]/3: a virtual call of
// base::call(int &&) reaches the final overrider func::call(int &&).  The
// front end's thunk for it passed its parameter `a', an lvalue, to the
// overrider's rvalue reference parameter; the conversion failed, and in a
// system header (where such failures drop the body) the virtual call
// returned a nondeterministic value.  libc++'s std::function calls
// __base<R(Args...)>::operator()(Args &&...) virtually.
# 1 "/usr/include/cbmc_test_virtual_rvalue_reference.h" 1 3
struct base
{
  virtual int call(int &&a) = 0;
};
struct func : base
{
  int call(int &&a)
  {
    return a + 1;
  }
};
# 21 "main.cpp" 2
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  func fn;
  base &b = fn;
  __CPROVER_assert(b.call(1) == 2, "called");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
