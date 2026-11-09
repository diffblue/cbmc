const int months = 12;

int main()
{
  char *p;
  __CPROVER_assume(__CPROVER_w_ok(p, 1));
  *p = 123; // should not alias 'months', as we are writing
  __CPROVER_assert(months == 12, "property 1");
}
