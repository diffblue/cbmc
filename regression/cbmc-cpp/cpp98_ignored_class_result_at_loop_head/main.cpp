// N5008 [stmt.expr]/1, [class.temporary]/2: the discarded result of
// `insert(...)' is a temporary of class type, materialized (here: the
// object the callee constructs its return value in) for each evaluation,
// also when the call is the first statement of a loop body that the loop
// jumps back to.  The declaration of that object was placed before the
// jump target, so from the second iteration on it was dead.
extern "C" void __CPROVER_assert(bool, const char *);
struct It
{
  int *n;
  explicit It(int *x) : n(x)
  {
  }
  ~It()
  {
  }
};
It insert(int *p, int v)
{
  *p += v;
  return It(p);
}
int main()
{
  int total = 0;
  int i = 0;
  do
    insert(&total, i);
  while(++i < 3);
  __CPROVER_assert(total == 3, "inserted");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
