
int main()
{
  int i, j=20;

  if(i>=20)
    __CPROVER_assert(i >= 10, "i>=10"); // success

  if(i>=10 && i<=20)
    __CPROVER_assert(i != 30, "i!=30"); // success

  if(i>=10 && i<=20)
    __CPROVER_assert(i != 15, "i!=15"); // fails

  if(i<1 && i>10)
    __CPROVER_assert(0, "0"); // success

  if(i>=10 && j>=i)
    __CPROVER_assert(j >= 10, "j>=10"); // success

  if(i>=j)
    __CPROVER_assert(i >= j, "i>=j"); // unknown

  if(i>10)
    __CPROVER_assert(i >= 11, "i>=11"); // success

  if(i<=100 && j<i)
    __CPROVER_assert(j < 100, "j<100"); // success
}
