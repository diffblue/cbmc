// N5008 [dcl.type.simple], [over.oper.general]/1: an operator-function-id
// does not name a type, so the statement `operator[](to)(operator[](from));'
// is an expression statement: the explicit call `operator[](to)' and a call
// of its result with operator().  The parser took `operator[]' as a
// decl-specifier and `(to)(...)' as a declarator, then failed: "found no
// match for symbol 'operator[]'" (CBMC's own event_grapht::copy_segment,
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct ev
{
  int v = 0;
  void operator()(const ev &o)
  {
    v = o.v + 1;
  }
};
struct graph
{
  ev nodes[3];
  ev &operator[](int n)
  {
    return nodes[n];
  }
  void copy(int to, int from)
  {
    // N5008 [over.call]: the result of the explicit operator function call
    // `operator[](to)' is called with operator()
    operator[](to)(operator[](from));
  }
};
int main()
{
  graph g;
  g.nodes[1].v = 4;
  g.copy(2, 1);
  __CPROVER_assert(g.nodes[2].v == 5, "call of the operator[] result");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
