int g, b;
int result;

int main(void)
{
  result = 0;
  switch(g)
  {
    if(b)
    {
    case 1:
      result = 1;
      break;
    }
  }
  // In C, a case label is a jump target inside the switch body.
  // Jumping to case 1 enters the if branch regardless of b.
  if(g == 1)
    __CPROVER_assert(result == 1, "case 1 reached when g==1");
  return 0;
}
