int main(void)
{
  int in;
  int out1;
  int a;

#ifdef INEQ
  if(in > 0)
#else
  if(in == 0)
#endif
  {
    int q = 1;
  }

  if(in == 1)
    a++;

  out1 = a;
}
