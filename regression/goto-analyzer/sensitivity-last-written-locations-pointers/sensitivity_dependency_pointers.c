void do_pointers()
{
  int bool_;
  int bool_1;
  int bool_2;

  int x = 10;
  int *x_p;

  int y = 20;
  int *y_p;

  x_p = &x;

  *x_p = 30;
  x = 40;

  *x_p = *y_p;
  x = 50;
  y_p = &x;

  *x_p = 60;

  int j = *y_p;
}

int main()
{
  do_pointers();
}
