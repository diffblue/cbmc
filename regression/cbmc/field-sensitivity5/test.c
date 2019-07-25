#include <assert.h>

struct A
{
  int head;
  struct A *tail;
};

int main(int argc, char **argv)
{
  struct A node1, node2, node3;
  node1.tail = argc % 2 ? &node2 : &node3;
  node2.tail = argc % 3 ? &node1 : &node3;
  node3.tail = argc % 5 ? &node1 : &node2;
  node1.tail->tail->tail->head = argc;
  assert(node1.head == argc);
}
