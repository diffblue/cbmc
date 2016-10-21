#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct list 
{
  int key;
  struct list *next;
} mlist;

mlist *head;

mlist* search_list(mlist *l, int k)
{
  l = head;
  while(l!=NULL && l->key!=k)
  {
    l = l->next;
  }
  return l;
}

int delete_list(mlist *l)
{
  mlist *tmp;
  tmp = head;
  if (head != l)
  {
    while(tmp->next!=l)
      tmp = tmp->next;
      tmp->next = l->next;
  }
  else
  {
    head = l->next;
  }
  free(l);
  return 0;
}

int insert_list(mlist *l, int k)
{
  l = (mlist*)malloc(sizeof(mlist));
  if (head==NULL)
  {
    l->key = k;
    l->next = NULL;
  }
  else
  {
    l->key = k;
    l->next = head;
  }
  head = l;
  return 0;
}

int main(void)
{
  int i;
  mlist *mylist, *temp;
  insert_list(mylist,2);
  insert_list(mylist,5);
  insert_list(mylist,1);
  insert_list(mylist,3);
  mylist = head;
  temp = search_list(mylist,2);
  assert(temp->key == 2);
  delete_list(temp);
}
