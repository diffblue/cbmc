// N5008 [dcl.init.aggr]/3.1, /5: a designated-initializer-list for a base
// element initializes the named members; the others from their default
// member initializers or by value-initialization
extern "C" void __CPROVER_assert(bool, const char *);
struct A
{
  int a;
  int b = 7;
  int c;
};
struct D : A
{
  int d;
};
int main()
{
  D d{{.a = 2}, 4};
  __CPROVER_assert(
    d.a == 2 && d.b == 7 && d.c == 0 && d.d == 4, "designated base element");
  D e{{.a = 1, .c = 3}, 5};
  __CPROVER_assert(e.a == 1 && e.b == 7 && e.c == 3, "two designators");
  __CPROVER_assert(d.c == 3, "WRONG (must FAIL)");
}
