
int main()
{
  int x;
  int y;
  int i;

  // l1
  x = 0;

  for (i = 0; i < 10; i++)
  {
    if (i)
    {
      y = 1;
    }
    else
    {
      y = 2;
    }
  }

  if (y)
  {
    // l2
    x = 1;
  }

  if (i)
  {
    y = 8;
  }
  else
  {
    y = 9;
  }
  
  // l3
  x = 2;

  return 0;
}

