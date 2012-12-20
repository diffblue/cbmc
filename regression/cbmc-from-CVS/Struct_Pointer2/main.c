#include <stdlib.h>
#include <assert.h>

struct mylist
{
  int  data;
  struct mylist *next;
};

int main()
{
  struct mylist *p;

  // Allocations:
  p=malloc( sizeof(struct mylist ) );  
  p->data=1;
  p->next=malloc( sizeof(struct mylist ) );  
  p->next->data=2;
  p->next->next=malloc( sizeof(struct mylist ) );    
  p->next->next->data=3;
  p->next->next->next=malloc( sizeof(struct mylist ) );    
  p->next->next->next->data=4;
  
  assert(p->next->next->data==3);

  return 0;
}
