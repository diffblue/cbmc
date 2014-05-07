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
  Data* aux;

  Node *res, *err;
	__CPROVER_assume(res!=err);
	
	y = malloc(sizeof(*y));
	free(y);
	not_null(y);	
	//y->pData = y->data;
	aux = y->data;
	y->pData = aux;
	assert(res!=err);
}
