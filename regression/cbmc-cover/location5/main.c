#include <stdio.h>
#include <assert.h>
#include "single-linked-list.h"

int main(void)
{

	int i;
	mlist *mylist, *temp;

	insert_list(mylist,2);
	insert_list(mylist,5);
	insert_list(mylist,1);
	insert_list(mylist,3);

	mylist = head;

	printf("list all elements: ");
	while(mylist)
	{
		printf("%d ", mylist->key);
		mylist = mylist->next;
	}
	printf("\n");

	temp = search_list(mylist,2);
	printf("search for element 2: %s\n", temp->key == 2 ? "found" : "not found");
	assert(temp->key == 2);

	delete_list(temp);

	mylist = head;

	printf("list all elements except 2: ");
	while(mylist)
	{
		printf("%d ", mylist->key);
		mylist = mylist->next;
	}
	printf("\n");
}
