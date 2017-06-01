#include <stddef.h>

struct S
{
  int x;
  union {
    int y;
    struct S2
    {
      int z;
    } s[1];
  } u[2];
};

int main()
{
  int A[offsetof(struct S, u[0].y)==sizeof(int)?1:-1];
#if defined(__GNUC__) && !defined(__clang__)
  int B[offsetof(struct S, u->y)==sizeof(int)?1:-1];
  int C[offsetof(struct S, u->s[0].z)==sizeof(int)?1:-1];
#endif
  return 0;
}
