#include <assert.h>
#include <stdio.h>

int main(void)
{
  // C11 7.21.7.8: putchar returns the character written, which is
  // (unsigned char)c per 7.21.7.3 (fputc).
  int r1 = putchar((char)0xe9);
  if(r1 != EOF)
    assert(r1 == 0xe9); // (unsigned char)(char)0xe9

  int r2 = putchar(300);
  if(r2 != EOF)
    assert(r2 == (unsigned char)300); // 300 & 0xFF == 44

  return 0;
}
