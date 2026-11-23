const int months = 12;

int main()
{
  int *p;
  p = (int *)&months;
  *p = 123; // unsafe, since 'months' is const
}
