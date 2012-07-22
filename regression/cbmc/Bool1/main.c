#include <assert.h>

int main() {
  _Bool b1, b2, b3;
  
  b1=0;
  b1++;
  assert(b1);
  
  b2=1;
  b2+=10;
  assert(b2);
  
  b3=b1+b2;
  assert(b3==1);
  
  // a struct of _Bool
  struct
  {
    _Bool f1, f2, f3;
    _Bool f4: 1, f5: 1;
  } s;

  assert(sizeof(s)==4);
  
  s.f1=2;
  assert(s.f1==1);
  
  s.f4=1;
  assert(s.f4);
  
  *((unsigned char *)(&s.f2))=1;
  assert(s.f2);
}
