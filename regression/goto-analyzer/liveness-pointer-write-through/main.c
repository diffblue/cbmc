int main()
{
  int non_det;
  int x = 0;
  int *p = &x;

  if(non_det)
    *p = 2;
  else
    *p = 3;
}
