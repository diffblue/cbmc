#ifndef SINGLE_LINKED_LIST_H_
#define SINGLE_LINKED_LIST_H_

typedef struct list {
	int key;
	struct list *next;
} mlist;

mlist *head;
mlist* search_list(mlist *l, int k);
int delete_list(mlist *l);
int insert_list(mlist *l, int k);

#endif /* SINGLE_LINKED_LIST_H_ */
