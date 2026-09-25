#pragma pack(push)
#pragma pack(1)
typedef struct
{
  int data[2];
} arr;

typedef struct
{
  arr vec[2];
} arrvec;
#pragma pack(pop)

int main()
{
  arrvec A;
  arrvec *x = &A;
  __CPROVER_assume(x->vec[1].data[0] < 42);
  unsigned k = __VERIFIER_nondet_unsigned();
  __CPROVER_assert(k != 2 || ((int *)x)[k] < 42, "");
}
