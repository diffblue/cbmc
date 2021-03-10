typedef unsigned B[8];

void fun(B b) {
}

int main(void)
{
  B var;
  unsigned *p1 = &var;
  unsigned *p2 = var;
  fun(p1);
}
