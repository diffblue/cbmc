 #include <assert.h>
 
typedef struct
{
  char a;
  int b;
} S1t;
 
int main ()
{
  S1t* mem[4];

  S1t s;
  mem[3]=&s;

  // this should fail; these are uninitialized
  assert(mem[1]->b == mem[2]->b);

  return 0;
}
