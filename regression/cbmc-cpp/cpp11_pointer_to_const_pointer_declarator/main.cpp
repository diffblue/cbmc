// N5008 [dcl.ptr]/1: in `T * cv1 * D' the first `*' with its cv1 forms the
// type "cv1 pointer to T" and the second `*' a pointer to THAT --
// `int *const *q' declares q as a (modifiable) pointer to a const pointer
// to int.  The parser folded the ptr-operators in the wrong order and put
// the const on q itself: `++q' was rejected ("'q' is constant"; CBMC's own
// code through `node *const *' iterator members, dog-fooding), and `*q =
// 0' was accepted.
extern "C" void __CPROVER_assert(bool, const char *);
struct node
{
  int v;
};
struct holder
{
  node *const *p;
};
int main()
{
  node a{1}, b{2};
  node *arr[2] = {&a, &b};
  node *const *q = arr; // local: pointer to const pointer
  ++q;
  holder h{arr};
  ++h.p; // member of the same type
  __CPROVER_assert(
    (*q)->v == 2 && (*h.p)->v == 2, "pointer to const pointer is modifiable");
  const char *const names[] = {"a", "bc"};
  const char *const *argv = names;
  ++argv;
  __CPROVER_assert(argv[0][1] == 'c', "argv-style pointer");
  int x = 1;
  int *px = &x;
  int *const *cq = &px;
  **cq = 5; // the int is not const
  __CPROVER_assert(x == 5, "pointee of the const pointer is modifiable");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
