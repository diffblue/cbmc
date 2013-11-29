typedef unsigned B[8];

void fun(B)
{
}

int main(void)
{
  B var;
  unsigned *p = var;
  fun(p);
}
