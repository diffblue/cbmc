#include <stdlib.h>

struct node
{
    int value;
    struct node *next;
};

struct list
{
  int size;
  struct node *head;
};

void removeLast(struct list * l)
{
  int index = l->size - 1;
  struct node **current;
  for(current = &(l->head); index && *current; index--)
    current = &(*current)->next;
  *current = (*current)->next;
  l->size--;
}

int main () {
  //build a 2-nodes list
  struct node *n0 = malloc(sizeof(struct node));
  struct node *n1 = malloc(sizeof(struct node));
  struct list *l = malloc(sizeof(struct list));
  l->size = 2;
  l->head = n0;

  n0->next=n1;
  n1->next=NULL;

  //remove last node from list

  //this passes
  // struct node **current = &(l->head);
  // current = &(*current)->next;
  // *current = (*current)->next;
  // l->size--;
  //this doesn't
  removeLast(l);

  __CPROVER_assert(n0->next == NULL , "not NULL");
}
