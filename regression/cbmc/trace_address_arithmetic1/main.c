#include <assert.h>

typedef struct
{
  int inta;
  int intb;
} struct_t;

typedef union {
  int intaa;
  struct_t structbb;
} union_struct_t;

int main()
{
  union_struct_t uuu;
  char *ptr = (char *)&uuu.structbb.intb;
  int A[2];
  int *ip = &A[1];
  uuu.structbb.intb = 1;
  assert(0);
}
