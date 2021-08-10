struct S
{
  int x;
  int y;
};

int main()
{
  int non_det;
  struct S s = {1, 3};

  if(non_det)
    s.x = 2;
  else
    s.x = 3;
}
