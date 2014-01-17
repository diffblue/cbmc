/*
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>
#include "../heap_builtins.h"

struct TreeNode {
	struct TreeNode* left;
	struct TreeNode* right;
};

struct TreeNode *res, *err;

#define not_null(x) if(x == NULL) res = err;

extern __CPROVER_bool nondet();


void main() {

	struct TreeNode* root = malloc(sizeof(*root)), *n;

	__CPROVER_assume(res!=err);

	not_null(root);	
	root->left = NULL;
	not_null(root);	
	root->right = NULL;

	while (nondet()) {
		n = root;
		not_null(n);	
		while (/*n->left &&*/ n->right) { // BUG found with 2 unwindings
		  if (nondet()) {
		    not_null(n);	
		    n = n->left;
		  }
		  else {
		    not_null(n);	
		    n = n->right;
		  }
		  not_null(n);	
		}
		not_null(n->left);	
		if (!n->left && nondet()) {
		  	not_null(n);	
			n->left = malloc(sizeof(*n));
                        struct TreeNode* auxleft = n->left;				
			not_null(auxleft);
			auxleft->left = NULL;
			not_null(auxleft);				
			auxleft->right = NULL;
		}
		not_null(n);				
		if (!n->right && nondet()) {
			not_null(n);				
			n->right = malloc(sizeof(*n));
                        struct TreeNode* auxright = n->right;				
			not_null(auxright);				
			auxright->left = NULL;
			not_null(auxright);				
			auxright->right = NULL;
		}
	}

	n = NULL;

	struct TreeNode* pred;

	while (root) {
		pred = NULL;
		n = root;
		not_null(n);				
		while (n->left || n->right) {
			pred = n;
			not_null(n);				
			if (n->left) {
	  			not_null(n);				
				n = n->left;
			    
			}
			else {
	  			not_null(n);				
				n = n->right;
			}
		}
		if (pred) {
  			not_null(pred);				
			if (n == pred->left) {
	  			not_null(pred);				
				pred->left = NULL;
			}
			else {
	  			not_null(pred);				
				pred->right = NULL;
			}
		} else
			root = NULL;
		free(n);
		//assert(!__CPROVER_HEAP_dangling(n));
	}


	assert(res!=err);
	//return 0;

}
