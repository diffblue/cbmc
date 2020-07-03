int global_x; // Should assign to 0.

void do_variables()
{
  int bool_;
  int bool_1;
  int bool_2;

  global_x = 5;

  // Simple variables.
  int x = 10;
  int y = 20;
  x = 30;
  y = 40;
  y = x;
  x = y;
  x = 5;
  x = x + 10;
  y = 10;

  if(bool_)
  {
    x = 20;
  }
  else
  {
    x = 20;
  }

  x = 50;

  if(bool_)
  {
    x = 20;
  }
  else
  {
    x = 30;
  }

  x = 0;

  if(bool_1)
  {
    x = 3;
    if(bool_2)
    {
      x = 5;
    }
  }
  else
  {
    x = 7;
  }
  y = 10;
  x = 20;
}

int main()
{
  do_variables();
}
