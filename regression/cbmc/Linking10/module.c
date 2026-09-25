// TU2: struct A is complete, struct B is incomplete
// Param 1 (struct A *): old=incomplete, new=complete -> set_to_new=true
// Param 2 (struct B *): old=complete, new=incomplete -> set_to_new=false
// Without |= accumulation, replace would be false (from param 2),
// losing the replacement needed for param 1.
struct A
{
  int x;
};
struct B;

void f(struct A *a, struct B *b)
{
  if(a)
    __CPROVER_assert(a->x == 0, "a->x accessible");
}
