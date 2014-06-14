#include <assert.h>

enum { ASD1, ASD2 } e;

int main()
{
  const char *p;
  
  e=ASD1;
  
  p=({ const char *tmp;
     switch(e) { case ASD1: tmp="abc"; } tmp; });

  assert(p[0]=='a');  
  assert(p[1]=='b');  
  assert(p[2]=='c');  
  assert(p[3]==0);
}
