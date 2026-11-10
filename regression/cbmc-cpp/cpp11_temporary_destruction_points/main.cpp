// N5008 [class.temporary]/4: temporaries are destroyed as the last step of
// the full-expression; /6: a temporary bound to a reference is destroyed at
// the end of the reference's lifetime.  Observed through a destructor
// counter.
extern "C" void __CPROVER_assert(bool, const char *);
int g_dtor = 0;
struct T
{
  int v;
  T(int x) : v(x)
  {
  }
  ~T()
  {
    g_dtor++;
  }
};
int main()
{
  {
    T(7);
    __CPROVER_assert(g_dtor == 1, "/4 end of full-expression");
    const T &k = T(8);
    __CPROVER_assert(g_dtor == 1, "/6 not yet destroyed");
    __CPROVER_assert(k.v == 8, "/6 value");
  }
  __CPROVER_assert(g_dtor == 2, "/6 destroyed with the reference");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
