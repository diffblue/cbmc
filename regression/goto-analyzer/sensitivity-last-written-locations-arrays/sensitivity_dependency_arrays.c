void do_arrays()
{
  int bool_;
  int bool_1;
  int bool_2;

  int x[2];

  // Simple variables.
  x[0] = 10;
  x[1] = 20;
  x[0] = 30;
  x[1] = 40;
  x[1] = x[0];
  x[0] = x[1];
  x[0] = 5;
  x[0] = x[0] + 10;
  x[1] = 10;

  if(bool_)
  {
    x[0] = 20;
  }
  else
  {
    x[0] = 20;
  }

  x[0] = 0;

  if(bool_1)
  {
    x[0] = 3;
    if(bool_2)
    {
      x[0] = 5;
    }
  }
  else
  {
    x[0] = 7;
  }
  x[1] = 10;
  x[0] = 20;
}

int main()
{
  do_arrays();
}
