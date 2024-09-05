void __assert_fail(char *, char *, unsigned, char *);

int main()
{
  (void)((1 < 2) || (__CPROVER_assert(0, ""), 0));

  int jumpguard;
  jumpguard = (jumpguard | 1);
label_1:;
  {
    while(1)
    {
      if(jumpguard == 0)
      {
        __assert_fail("0", "lc2.c", 8U, "func");
        goto label_1;
      }
      goto label_2;
    }
  label_2:;
  }
}
