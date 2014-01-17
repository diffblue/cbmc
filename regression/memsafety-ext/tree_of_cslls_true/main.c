/*
 * A tree of circular singly linked lists
 *
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>
//#include "../heap_builtins.h"

#define not_null(x) if(x == NULL) res = err;

typedef struct TListNode
{
	struct TListNode* next;
} ListNode;

typedef struct TTreeNode
{
	struct TTreeNode* left;
	struct TTreeNode* right;
	ListNode* list;
} TreeNode;

struct TreeNode* res, *err;

extern __CPROVER_bool nondet();


void main()
{

	__CPROVER_assume(res!=err);

	TreeNode* tree = malloc(sizeof(*tree));
	TreeNode* tmp;
	ListNode* tmpList;

	not_null(tree);				
	tree->left  = NULL;
	not_null(tree);				
	tree->right = NULL;
	not_null(tree);				
	tree->list = malloc(sizeof(ListNode));
	not_null(tree);		
        ListNode* auxlist;
//__CPROVER_assume(__CPROVER_HEAP_dangling(auxlist));
        auxlist = tree->list;		
	not_null(auxlist);				
	auxlist->next = tree->list;
	
	while (nondet())
	{
		tmpList = malloc(sizeof(ListNode));
		not_null(tmpList);				
		not_null(tree);				
		//not_null(tree->list);				
		tmpList->next = tree->list->next;
		not_null(tree);				
                ListNode* auxlist = tree->list;		
		not_null(auxlist);				
		auxlist->next = tmpList;
	}

	while (nondet())
	{
	  tmp = tree;

		not_null(tmp);				
		while ((NULL != tmp->left) && (NULL != tmp->right))
		{
			if (nondet())
			{
			  not_null(tmp);				
			  tmp = tmp->left;
			}
			else
			{
			  not_null(tmp);				
			  tmp = tmp->right;
			}
			not_null(tmp);				
		}

		TreeNode* newNode;
		not_null(tmp);				
		if ((NULL == tmp->left) && nondet())
		{
			newNode = malloc(sizeof(*newNode));
			not_null(tmp);				
			tmp->left = newNode;
		}
		else if ((NULL == tmp->right) && nondet())
		{
		        newNode = malloc(sizeof(*newNode));
			not_null(tmp);				
			tmp->right = newNode;
		}
		else
		{
			continue;
		}

		not_null(newNode);				
		newNode->left = NULL;
		not_null(newNode);				
		newNode->right = NULL;
		not_null(newNode);				
		newNode->list = malloc(sizeof(*newNode->list));
		not_null(newNode);
                ListNode* auxlist = newNode->list;				
		not_null(auxlist);				
		auxlist->next = newNode->list;

		while (nondet())
		{
			tmpList = malloc(sizeof(ListNode));
			not_null(tmpList);				
			not_null(tree);				
			//not_null(tree->list);				
			tmpList->next = tree->list->next;
			not_null(tree);				
                        ListNode* auxlist = tree->list;		
			not_null(auxlist);				
			auxlist->next = tmpList;
		}
	}

	while (NULL != tree)
	{	// while there are still some remains of the tree
		tmp = tree;
		TreeNode* pred = NULL;

		not_null(tmp);				
		while ((NULL != tmp->left) || (NULL != tmp->right))
		{
			pred = tmp;
			not_null(tmp);				
			if (NULL != tmp->left)
			{
			  not_null(tmp);				
			  tmp = tmp->left;
			}
			else
			{
			  not_null(tmp);				
			  tmp = tmp->right;
			}
			not_null(tmp);				
		}

		if (NULL != pred)
		{
		        not_null(pred);				
			if (tmp == pred->left)
			{
			  not_null(pred);				
			  pred->left = NULL;
			}
			else
			{
			  not_null(pred);				
			  pred->right = NULL;
			}
		}
		else
		{
			tree = NULL;
		}

	        not_null(tmp);				
	        //not_null(tmp->list);				
		while (tmp->list != tmp->list->next)
		{
		  not_null(tmp);				
                  ListNode* auxlist = tmp->list;		
		  not_null(auxlist);				
		  tmpList = auxlist->next;
		  not_null(auxlist);				
		  not_null(tmpList);		
		  auxlist->next = tmpList->next;
		  free(tmpList);
		  not_null(tmp);				
		  //not_null(tmp->list);				
		}

		not_null(tmp);				
		free(tmp->list);
		free(tmp);
	}
	
	assert(res!=err);

	//return 0;
}
