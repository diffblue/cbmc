int nondet_int();
int x;

int main()
{
  x = nondet_int();
  __CPROVER_assert(x != 20, "property 1"); // fails
}
