struct S
{
  int len;
};

__CPROVER_bool nondet_bool();

int main()
{
  struct S *s_p = 0;
  struct S s;
  if(nondet_bool())
    s_p = &s;
  s_p->len = s_p->len + 1;
  __CPROVER_assert(0, "");
}
