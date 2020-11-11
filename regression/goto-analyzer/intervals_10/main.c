
int main()
{
  int i, j;

  if(i<=100 && j<i)
    __CPROVER_assert(j <= 100, "j<=100");

  if(i<=100 && j<i)
    __CPROVER_assert(j < 101, "j<101");

  if(i<=100 && j<i)
    __CPROVER_assert(j > 100, "j>100"); // fails

  if(i<=100 && j<i)
    __CPROVER_assert(j < 99, "j<99"); // fails

  if(i<=100 && j<i)
    __CPROVER_assert(j == 100, "j==100"); // fails
}
