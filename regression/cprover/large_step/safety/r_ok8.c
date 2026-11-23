char ch;

int main()
{
  __CPROVER_assert(__CPROVER_r_ok(&ch, 1), "property 1");     // passes
  __CPROVER_assert(__CPROVER_r_ok(&ch + 1, 1), "property 2"); // fails
  __CPROVER_assert(__CPROVER_r_ok(&ch + 1, 0), "property 3"); // passes
  __CPROVER_assert(__CPROVER_r_ok(&ch + 2, 0), "property 4"); // fails
}
