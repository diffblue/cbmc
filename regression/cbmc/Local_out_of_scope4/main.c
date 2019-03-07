int g;

int main()
{
  for(int i = 0; i < 4; ++i)
  {
    int *x;
    *&x = &g;
  }
}
