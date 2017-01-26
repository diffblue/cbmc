
int x;

int main()
{
  int i;

  goto L1;
  for (i = 0; i < 3; i++) // not handled
  {
    L1: ;
  }

  for (i = 0; i < 3; i++) // handled
  {
    goto L2;
  }
  x = 0;
  L2: ;
}

