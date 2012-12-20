#include <cassert>

const char my_string[]="abc123";

int main()
{
  assert(my_string[0]=='a');
  assert(my_string[6]==0);
  assert(sizeof(my_string)==7);
}
