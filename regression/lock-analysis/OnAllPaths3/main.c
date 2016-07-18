
int main()
{
  int x;
  int y;
  int i;

  for (i = 0; i < 10; i++)
  {
    if (i)
    {
      // l1
      x = 0;
    }
    else
    {
      y = 2;
    }
  }

  // l2
  x = 1;

  if (i)
  {
    y = 8;
  }
  else
  {
    y = 9;
  }
  
  while (!y)
  {
    // l3
    x = 2;
  }

  return 0;
}

