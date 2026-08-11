// N5008 [dcl.fct]/6: `B...` with B a non-pack template parameter is
// B followed by C varargs.  With an unrelated trailing template pack
// (R) deduced empty, CBMC's empty-pack parameter removal dropped the
// varargs parameter and the call stopped resolving.
extern "C" void __CPROVER_assert(bool, const char *);
struct op
{
  template <class F, class B, class... R> int operator()(F, B...)
  {
    return 7;
  }
};
int main()
{
  op o;
  __CPROVER_assert(o(0UL, 1L) == 7, "trailing pack param deduction");
  return 0;
}
