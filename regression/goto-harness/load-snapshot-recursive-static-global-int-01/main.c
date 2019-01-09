int x;
int flag;

int main()
{
  x = 0;

  assert(flag != 0 || x == 1);
  assert(flag != 1 || x == 0);

  if(flag == 0)
  {
    flag = 1;
    main();
  }

  return 0;
}
