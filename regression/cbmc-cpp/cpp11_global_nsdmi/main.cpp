// N5008 [class.default.ctor]/3 + [basic.start.static]: a class with a default
// member initializer (NSDMI) has a non-trivial default constructor.  A
// namespace-scope (or file-static) object defined without an initializer must
// run that constructor, so its members take their declared defaults rather than
// being left merely zero-initialized.  Members without an NSDMI keep their
// static zero-initialization ([basic.start.static]/2).

extern "C" void __CPROVER_assert(int, const char *);

struct single
{
  int t = 5;
};

struct pair_t
{
  int t = 5;
  int u = 9;
};

struct mixed
{
  int t = 5; // NSDMI -> 5
  int u;     // no NSDMI -> static zero-initialized -> 0
};

single g_single;
pair_t g_pair;
mixed g_mixed;
static single g_file_static;

int main()
{
  __CPROVER_assert(g_single.t == 5, "global NSDMI applied");
  __CPROVER_assert(g_pair.t == 5, "global NSDMI first member");
  __CPROVER_assert(g_pair.u == 9, "global NSDMI second member");
  __CPROVER_assert(g_mixed.t == 5, "global NSDMI with a non-NSDMI member");
  __CPROVER_assert(g_mixed.u == 0, "non-NSDMI member zero-initialized");
  __CPROVER_assert(g_file_static.t == 5, "file-static NSDMI applied");

  // Non-vacuity guard: a deliberately wrong property that must FAIL.  Before
  // the fix the value-less global was statically zero-initialized, so this
  // assertion would have SUCCEEDED (g_single.t == 0) -- a false pass.
  __CPROVER_assert(g_single.t == 0, "WRONG: must fail");

  return 0;
}
