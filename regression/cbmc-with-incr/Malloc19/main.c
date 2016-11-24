// CBMC reports a counterexample yet the assertion should hold
//
// Counterexample is not reported anymore when doing one or more of:
// - removing 'int value' from the struct node
// - replacing the malloc by static allocation
// - replacing the conditional in line 32 by 'hd = gl_list.next'

#include <assert.h>

struct list_head {
	struct list_head *next;
};

struct node {
    int value;
    struct list_head linkage;
};

struct list_head gl_list;

int main()
{
    // Create node
    struct node *nd;
    nd = (struct node *)__CPROVER_malloc(sizeof(struct node));

    // Link node
    struct list_head *hd = &(nd->linkage);
    gl_list.next = hd;
    hd->next = &gl_list;

    hd = (gl_list.next == &gl_list) ? 0 : gl_list.next; // always returns gl_list.next

    // Delete node
    hd = hd->next; // then: hd == &gl_list
    hd->next = hd; // then: gl_list.next == &gl_list

    // In the generated constraints, CBMC takes for the value of gl_list.next
    // the value assigned in line 29. But gl_list.next is changed through a
    // pointer in line 36.
    assert(gl_list.next == &gl_list); // Holds

    return 0;
}

