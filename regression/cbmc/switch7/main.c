// These need to be constant-folded at compile time

#define C1 (int)(0. / 1. + 0.5)
#define C2 (int)(1. / 1. + 0.5)

int nondet_int();

int main(void)
{
  int i = nondet_int();

  switch(i)
  {
  case C1:
    break;

  case C2:
    break;

  default:
    break;
  }
}
