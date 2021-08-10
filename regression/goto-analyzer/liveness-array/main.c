int main()
{
  int non_det;
  int x[2] = {0, 1};

  if(non_det)
    x[0] = 2;
  else
    x[0] = 3;
}
