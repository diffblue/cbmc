#include <assert.h>

int main(int argc, char *argv[])
{
  // Test if we can represent constant chars
  char x='a';
  assert(x=='a');
  assert(x=='b');
  return 0;
}
