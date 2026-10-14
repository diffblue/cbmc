int g, b;
int result;

int main(void)
{
  result = 0;
  switch(g)
  {
    if(b)
    {
    default:
      result = 1;
      break;
    }
  case 0:
    break;
  }
  // When g is not 0, the default label is reached.
  if(g != 0)
    __CPROVER_assert(result == 1, "default reached when g!=0");
  return 0;
}
