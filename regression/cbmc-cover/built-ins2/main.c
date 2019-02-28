#include <string.h>

struct mystruct {
  int x;
  char y;
};

int main()
{
  struct mystruct s;
  char c;
  __CPROVER_input("c", c);

  memset(&s,c,sizeof(struct mystruct));

  if(s.y=='A')
  {
    return 0;
  }
  return 1;
}
