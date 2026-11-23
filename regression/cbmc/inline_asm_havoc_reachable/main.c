// Inline assembly that is not modeled may change all objects it can reach:
// with a "memory" clobber, everything reachable from objects of static
// lifetime and from address-taken local variables of all functions on the
// call stack, and otherwise everything reachable from its pointer operands.
#include <stdlib.h>

struct node
{
  int data;
  struct node *next;
};

struct node *head;

static void clobber(void)
{
  asm volatile("cli" ::: "memory");
}

static struct node *new_node(int data, struct node *next)
{
  struct node *n = malloc(sizeof(struct node));
  __CPROVER_assume(n != NULL);
  n->data = data;
  n->next = next;
  return n;
}

int main(void)
{
  struct node *b = new_node(2, NULL);
  struct node *a = new_node(1, b);

  // reachable from an object of static lifetime, two levels deep
  head = a;
  clobber();
  __CPROVER_assert(b->data == 2, "heap object reachable from static"); // fails
  __CPROVER_assert(head == a, "pointer in static");                    // fails
  __CPROVER_assert(
    head == a || head == b || head == NULL,
    "pointers are restricted to known values"); // holds
  if(head != NULL)
    head->data = 0; // no dereference failure

  // a local variable of a caller whose address is taken
  int local = 0;
  int *alias = &local;
  int unaddressed = 0;
  clobber();
  __CPROVER_assert(local == 0, "escaped local of caller");     // fails
  __CPROVER_assert(unaddressed == 0, "local without address"); // holds

  // without a "memory" clobber: only what the operands reach
  head = NULL;
  struct node *d = new_node(4, NULL);
  struct node *c = new_node(3, d);
  struct node *e = new_node(5, NULL);
  asm volatile("foo %0" : : "r"(c));
  __CPROVER_assert(d->data == 4, "heap object reachable from operand"); // fails
  __CPROVER_assert(e->data == 5, "unreachable heap object");            // holds

  return 0;
}
