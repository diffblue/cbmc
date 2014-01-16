/*
 * Tree destruction using a stack
 *
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>

struct TreeNode {
	struct TreeNode* left;
	struct TreeNode* right;
};

struct StackItem {
	struct StackItem* next;
	struct TreeNode* node;
};

struct TreeNode* res, *err;

#define not_null(x) if(x == NULL) res = err;

extern __CPROVER_bool nondet();


void main() {

	__CPROVER_assume(res!=err);

	struct TreeNode* root = malloc(sizeof(*root)), *n;
	not_null(root);	
	root->left = NULL;
	not_null(root);	
	root->right = NULL;

        root = root->right; // BUG (to be found with 2 unwindings)

	while (nondet()) {
		n = root;
		not_null(n);	
		while (n->left!=NULL && n->right!=NULL) {
                  
		  if (nondet()) {
		    not_null(n);	
		    n = n->left;
		  }
		  else {
		    not_null(n);	
		    n = n->right;
		  }

		  not_null(n);	
		  if (n->left==NULL && nondet()) {
		    not_null(n);	
		    n->left = malloc(sizeof(*n));
                    struct TreeNode* auxleft = n->left;
		    not_null(auxleft);	
		    auxleft->left = NULL;
		    not_null(auxleft);	
		    auxleft->right = NULL;
		  }
		  not_null(n);	
		  if (n->right==NULL && nondet()) {
    		    not_null(n);	
		    n->right = malloc(sizeof(*n));
                    struct TreeNode* auxright = n->right;
		    not_null(auxright);	
		    auxright->left = NULL;
		    not_null(auxright);	
		    auxright->right = NULL;
		  }
		  not_null(n);	
		}
	}

	n = NULL;

	struct StackItem* s = malloc(sizeof(*s)), *st;
	not_null(s);	
	s->next = NULL;
	not_null(s);	
	s->node = root;

	while (s != NULL) {
		st = s;
		not_null(s);	
		s = s->next;
		not_null(st);	
		n = st->node;
		free(st);
		not_null(n);	
		if (n->left!=NULL) {
			st = malloc(sizeof(*st));
			not_null(st);	
			st->next = s;
			not_null(st);	
			not_null(n);	
			st->node = n->left;
			s = st;
		}
		not_null(n);	
		if (n->right!=NULL) {
			st = malloc(sizeof(*st));
			not_null(st);	
			st->next = s;
			not_null(st);	
			not_null(n);	
			st->node = n->right;
			s = st;
		}
		free(n);
	}

	assert(res!=err);
	//return 0;
}
