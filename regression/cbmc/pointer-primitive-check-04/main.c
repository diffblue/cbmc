
void main()
{
  char *p;
  __CPROVER_assume(__CPROVER_r_ok(p, 1));
}
