#include <assert.h>

typedef unsigned int u32;
typedef unsigned long long int u64;

typedef u32 (*myfuncptr)(u32 value);

u32 myfunc_1(u32 value1){
   return value1*2;
}

u32 myfunc_2(u32 value2){
   assert(value2==4);
   return value2*4;
}

int main(void){
  myfuncptr fptr = 0;
u32 value;


  assert(fptr == 0);

fptr=myfunc_1;
value=2;
value=fptr(value);    //value should be 4 after this
assert(value == 4);

fptr=myfunc_2;
value=fptr(value);    //value should be 16 after this
assert(value == 16);

}
