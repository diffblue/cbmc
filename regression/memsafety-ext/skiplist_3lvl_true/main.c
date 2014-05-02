/* 
 * A slightly obfuscated implementation of skip lists without using ordering and height counters.
 * For a better implementation, see, e.g., http://eternallyconfuzzled.com/tuts/datastructures/jsw_tut_skip.aspx
 * or http://ck.kolivas.org/patches/bfs/test/bfs406-skiplists.patch
 *
 * We assume the height to be fixed to 3 and we always have the maximum height at the head and tail
 * nodes---in other words, we do not let the height grow/shrink. Also, we do not consider a dynamic
 * number of next pointers in the nodes.
 *
 * This source code is licensed under the GPLv3 license.
 *
 * Taken from Forester.
 */

#include <stdlib.h>

#define not_null(x) if(x == NULL) res = err;

// a skip list node with three next pointers
struct sl_item {
	struct sl_item *n1, *n2, *n3;
};

// a skip list
struct sl {
	struct sl_item *head, *tail;
};

struct sl_item* res, *err;

extern sl_item* nondet_sl_item();
extern __CPROVER_bool nondet();

struct sl_item* alloc_or_die(void)
{
	struct sl_item *pi = malloc(sizeof(struct sl_item));

	return pi;
}

struct sl* create_sl_with_head_and_tail(void)
{
	struct sl *sl = malloc(sizeof(*sl));

	not_null(sl);
	sl->head = malloc(sizeof(struct sl_item));
	sl->tail = malloc(sizeof(struct sl_item));

	not_null(sl);
        struct sl_item * auxhead = sl->head;
	not_null(auxhead);
	auxhead->n3 = auxhead->n2 = auxhead->n1 = sl->tail;
	not_null(sl);
        struct sl_item * auxtail = sl->tail;
	not_null(auxtail);
	auxtail->n3 = auxtail->n2 = auxtail->n1 = NULL;

	return sl;
}

// The function inserts one node of a random height to a randomly chosen position in between of 
// the head and tail.
void sl_random_insert(struct sl *sl)
{
	// a1, a2, a3 remember the nodes before the inserted one at the particular levels
	struct sl_item *a1, *a2, *a3;
	struct sl_item *new;

	// moving randomly on the 3rd level
	not_null(sl);
	a3 = sl->head;
	not_null(a3);
	not_null(sl);
	while (a3->n3 != sl->tail && nondet()) {
	  	not_null(a3);
		a3 = a3->n3;
	  	not_null(a3);
	}

	// moving randomly on the 2nd level, not going behind a3->n3
	a2 = a3;
	not_null(a2);
	not_null(a3);
	while (a2->n2 != a3->n3 && nondet()) {
	  	not_null(a2);
		a2 = a2->n2;
	  	not_null(a2);
	}

	// moving randomly on the 1st level, not going behind a2->n2
	a1 = a2;
	not_null(a2);
	not_null(a1);
	while (a1->n1 != a2->n2 && nondet()) {
	  	not_null(a1);
		a1 = a1->n1;
	  	not_null(a1);
	}

	// allocation and insertion of a new node
	new = malloc(sizeof(struct sl_item));
	// always insert at level 1
	not_null(new);
	not_null(a1);
	new->n1 = a1->n1;
	not_null(a1);
	a1->n1 = new;

	// choose whether to insert at level 2
	if (nondet()) {
	        not_null(new);
		not_null(a2);
		new->n2 = a2->n2;
		not_null(a2);
		a2->n2 = new;
		// choose whether to insert at level 3
		if (nondet()) {
		  	not_null(new);
			not_null(a3);
			new->n3 = a3->n3;
			not_null(a3);
			a3->n3 = new;
		}
	}
}

void destroy_sl(struct sl *sl)
{
	struct sl_item *tmp;


	not_null(sl);
	while (sl->head) {
	        not_null(sl);
		tmp = sl->head;
               	not_null(sl);
		not_null(sl->head);
		sl->head = sl->head->n1;
		free(tmp);
	  	not_null(sl);
	}
	free(sl);
}

void main()
{
	struct sl *sl = create_sl_with_head_and_tail();

        res = nondet_sl_item();
        err = nondet_sl_item();
	__CPROVER_assume(res!=err);

	while (nondet())
		sl_random_insert(sl);

	destroy_sl(sl);

	assert(res!=err);

	//return 0;
}



