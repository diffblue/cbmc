#include <assert.h>

int main(int argc, char *argv[])
{
  // Test if we can represent constant chars
  char x='a';
  __CPROVER_assert(x == 'a', "x=='a'");
  __CPROVER_assert(x == 'b', "x=='b'");
  return 0;
}
