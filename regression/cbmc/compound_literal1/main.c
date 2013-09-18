#include <assert.h>

struct POINT { int x, y; };
union U { float f; int i; };

int main()
{
  // from http://www.drdobbs.com/the-new-c-compound-literals/184401404
  assert(((int) {1})==1);
  assert(((const int) {2})==2);
  assert(((float[2]) {2.7, 3.1})[1]==3.1f);
  assert(((struct POINT) {0, 1}).y==1);
  assert(((union U) {1.4}).f==1.4f);
  
  // address can be taken
  int *p=&(int){ 42 };
  assert(*p==42);
  
  // and modified
  *p=43;
  assert(*p==43);
  
  return 0;
}
