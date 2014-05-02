/*
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>
#include "../heap_builtins.h"

typedef struct TData
{
	char x;
} Data;

typedef struct TNode
{
	struct TNode* next;
	struct TNode* prev;
	Data* pData;
	Data* data;
} Node;


extern __CPROVER_bool nondet();

void main()
{
	Node* list = NULL;
	Node* y = NULL;

        Node *res, *err;
	__CPROVER_assume(res!=err);

	y = malloc(sizeof(*y));
	not_null(y);	
	y->next = NULL;
	not_null(y);	
	y->prev = NULL;
	
	not_null(y);	
	__CPROVER_assume(y->data!=NULL);
	y->pData = y->data;
	list = y;

	while (nondet())
	{
		y = malloc(sizeof(*y));
		not_null(y);	
		y->next = list;
		not_null(list);	
		list->prev = y;

		if (nondet())
		{
		  not_null(y);	
		  y->pData = malloc(sizeof(*y->pData));
		}
		else
		{
		  not_null(y);	
		  y->pData = y->data;
		  __CPROVER_assume(y->data!=NULL);
		}

		list = y;
	}

	while (NULL != list)
	{
		y = list;
		not_null(list);	
		list = list->next;

		not_null(y);	
		if (y->data != y->pData)
		{
  		  not_null(y);	
		  free(y->pData);
		}

                //this assertion fails: 
                //not_null(y); 
		free(y);
	}

	assert(res!=err);
	//return 0;
}
