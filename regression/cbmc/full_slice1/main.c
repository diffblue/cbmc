#include <assert.h>

typedef enum {
  A,
  B,
  C
} node_t;

void doit(node_t *node);

static inline void foo(node_t *node) { }
static inline void bar(node_t *node) { }

void doit(node_t *node) 
{
  switch (*node)
  {
  case A:
    foo(node);
    *node=B;
    bar(node);
    return;
  case C:
    *node=B;
    bar(node);
    return;
  }
}

int main() 
{
  node_t node=A;
  
  char count=0;  
  while(count++<10)
  {
    char c;    

    doit(&node);

    static char q=0;      
    q=0;
    
    if(c==0) 
    {
      assert(node == A);
    }
  }

  return 0;
}
