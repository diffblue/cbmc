#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "single-linked-list.h"

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

