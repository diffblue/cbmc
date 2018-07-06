#include <stdio.h>

int main()
{
  char ch;
  unsigned state=0;
  while((ch = getc(stdin)) != (char)-1)
  {
    switch(state)
    {
    case 0: if(ch=='<') state=1; else state=0; break;
    case 1: if(ch=='h') state=2; else state=0; break;
    case 2: if(ch=='t') state=3; else state=0; break;
    case 3: if(ch=='m') state=4; else state=0; break;
    case 4: if(ch=='l') state=5; else state=0; break;
    default:;
    }
  }
}
