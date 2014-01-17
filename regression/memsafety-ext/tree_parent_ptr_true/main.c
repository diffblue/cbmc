/*
 * Tree with parent pointers, destruction using a stack
 *
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>
#include "../heap_builtins.h"

struct TreeNode {
	struct TreeNode* left;
	struct TreeNode* right;
	struct TreeNode* parent;
};

struct StackItem {
	struct StackItem* next;
	struct TreeNode* node;
};

struct TreeNode* res, *err;

#define not_null(x) if(x == NULL || __CPROVER_HEAP_dangling(x)) res = err;

extern __CPROVER_bool nondet();


void main() {

	__CPROVER_assume(res!=err);

	struct TreeNode* root = malloc(sizeof(*root)), *n;
	not_null(root);
	root->left = NULL;
	not_null(root);
	root->right = NULL;
	not_null(root);
	root->parent = NULL;

	while (nondet()) {
		n = root;
		not_null(n);
		while (n->left && n->right) {
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

		not_null(n);
		if (!n->left && nondet) {
		        not_null(n);
			n->left = malloc(sizeof(*n));
                        struct TreeNode* auxleft = n->left;
		        not_null(auxleft);
			auxleft->left = NULL;
			auxleft->right = NULL;
			auxleft->parent = n;
		}
	        not_null(n);
		if (!n->right && nondet()) {
		        not_null(n);
			n->right = malloc(sizeof(*n));
                        struct TreeNode* auxright = n->right;
		        not_null(auxright);
			auxright->left = NULL;
			auxright->right = NULL;
			auxright->parent = n;
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
		if (n->left) {
			st = malloc(sizeof(*st));
			not_null(st);
			st->next = s;
			not_null(st);
			not_null(n);
			st->node = n->left;
			s = st;
		}
		not_null(n);
		if (n->right) {
			st = malloc(sizeof(*st));
			not_null(st);
			st->next = s;
			not_null(st);
			not_null(n);
			st->node = n->right;
			s = st;
		}
		not_null(n);
		free(n);
	}

	assert(res!=err);
	//return 0;
}
