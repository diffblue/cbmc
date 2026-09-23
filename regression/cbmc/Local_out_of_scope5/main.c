int main()
{
  int jumpguard;
  jumpguard = jumpguard | 1;
label_1:
  while(1)
  {
    int canary = 1;
    if(jumpguard == 0)
    {
      goto label_1;
    }
    __CPROVER_assert(canary, "should pass");
    break;
  }
}
