
void read(int, int*); // bodyless

int f(void)
{
  int t;

  read(1, &t); // set to t

  if (t < 0)
    t = 0;

  return t;
}

void main()
{
  f();
}

