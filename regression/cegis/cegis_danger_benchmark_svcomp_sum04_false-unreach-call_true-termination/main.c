#define a (2)
#define SIZE 8
int main(void) {
  int i;
  int sn=0;

  for(i=1; i<=SIZE; i++) {
    if (i<4)
    sn = sn + a;
  }

  __CPROVER_assert(sn==SIZE*a || sn == 0, "A");

  return 0;
}
