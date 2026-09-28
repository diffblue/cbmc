extern "C" void __CPROVER_assert(bool, const char *);
struct node
{
  int v;
};
struct point
{
  int x, y;
};
int main()
{
  // [expr.new]/24 + [dcl.init.list]/3.4: `new node{3}' aggregate-initializes
  // the single member from 3
  node *n = new node{3};
  __CPROVER_assert(n->v == 3, "single-element aggregate");
  point *p = new point{1, 2};
  __CPROVER_assert(p->x == 1 && p->y == 2, "two-element aggregate");
  __CPROVER_assert(n->v == 4, "WRONG (must FAIL)");
}
