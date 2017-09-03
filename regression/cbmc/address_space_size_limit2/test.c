#include <stdlib.h>
#include <assert.h>

int main(int argc, char** argv)
{
  char* c=(char*)malloc(10);
  char* d=c;
  for(char i=0; i<10; i++, d++);
  assert((size_t)d==(size_t)c+10);
}
