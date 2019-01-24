#include <assert.h>

int main(int argc, char *argv[])
{
  unsigned char x = argc;

  for(int i = 0; i < 3; ++i)
  {
    struct S
    {
      int a;
      int b[x + i + 1];
      int *c;
    } __attribute((packed));

    struct S s;

    for(int j = 0; j < i; ++j)
      s.b[x + j] = j;

    for(int j = 0; j < i; ++j)
      assert(s.b[x + j] == j);

    assert(
      sizeof(struct S) ==
      sizeof(int *) + ((unsigned char)argc + i + 2) * sizeof(int));
  }

  return 0;
}
