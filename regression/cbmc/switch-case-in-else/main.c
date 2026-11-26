int g, b;
int result;

int main(void)
{
  result = 0;
  switch(g)
  {
    if(b)
      result = 2;
    else
    {
    case 1:
      result = 1;
      break;
    }
  }
  if(g == 1)
    __CPROVER_assert(result == 1, "case 1 reached when g==1");
  return 0;
}
