//#include <cassert>

typedef int INT;

typedef enum { E1=1 } some_enum_type;

struct some_struct {
  unsigned int a:3;
  unsigned int b:1;
  signed int c:2;

  // an anonymous bitfield
  signed int :2;
  
  // with typedef
  INT x:1;
  
  // made of sizeof
  unsigned int abc: sizeof(int);

  // enums are integers!
  some_enum_type enum_field1 : 5;
  
  // and good as field sizes
  some_enum_type enum_field2 : E1;
} X;

int func(unsigned int) { return 1; }
int func(signed int) { return 2; }
int func(some_enum_type) { return 3; }
 
int main()
{
  assert(func(X.a)==1);
  assert(func(X.c)==2);
  assert(func(X.x)==2);
  assert(func(X.enum_field1)==3);
}
