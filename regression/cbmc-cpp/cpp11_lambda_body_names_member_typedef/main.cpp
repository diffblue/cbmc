// N5008 [expr.prim.lambda.closure]/13, [expr.prim.lambda.capture]/8: in a
// lambda inside a member function, a name of the enclosing class is looked
// up from the lambda's context; only non-static DATA members odr-used in the
// body are captured (through `this').  The closure lowering took every class
// component named in the body for a data member -- also a member typedef
// and a static member -- and type-checked it as a capture expression:
// `for(node_indext i = 0; ...)' failed with "symbol 'node_indext' does not
// uniquely resolve" (util/graph.h's grapht::output_dot, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct graph
{
  typedef unsigned long node_indext;
  static int scale;
  int n = 3;
  int out() const
  {
    int sum = 0;
    const auto each = [&sum](int count)
    {
      for(node_indext i = 0; i < node_indext(count); ++i)
        sum += i * scale;
    };
    each(n);
    const auto twice = [](node_indext i) -> node_indext { return 2 * i; };
    const auto member = [this] { return node_indext(n) + scale; };
    return sum + twice(5) + member();
  }
};
int graph::scale = 1;
int main()
{
  graph g;
  __CPROVER_assert(g.out() == 17, "class member typedef inside a lambda body");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
