// An alignment that is not a positive power of two must be rejected by the
// front-end (C11 6.2.8). This is the case left commented-out in
// gcc_attributes16/main.c; here it is exercised as a negative test.
struct __attribute__((aligned(5))) S
{
  int i;
};

struct S s;

int main(void)
{
  return 0;
}
