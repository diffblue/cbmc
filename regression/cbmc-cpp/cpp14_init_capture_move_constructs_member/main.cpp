// N5008 [expr.prim.lambda.capture]/6, /15, [dcl.type.auto.deduct]/3: an
// init-capture's member has the type deduced as for auto (not a
// reference) and is initialized by its constructor: an xvalue initializer
// moves, a plain capture by copy copies.
extern "C" void __CPROVER_assert(bool, const char *);
int moves = 0, copies = 0;
struct M
{
  M()
  {
  }
  M(const M &)
  {
    ++copies;
  }
  M(M &&)
  {
    ++moves;
  }
};
int main()
{
  M m;
  auto f = [q = static_cast<M &&>(m)] { return 0; };
  (void)f;
  __CPROVER_assert(moves == 1 && copies == 0, "the init-capture moved");
  auto g = [m] { return 0; };
  (void)g;
  __CPROVER_assert(moves == 1 && copies == 1, "the capture copied");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
