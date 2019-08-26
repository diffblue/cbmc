#include <assert.h>

struct A
{
  int data;
  struct A *children[2];
};

int main(int argc, char **argv)
{
  struct A root;
  struct A node1, node2;
  root.children[0] = argc % 2 ? &node1 : &node2;
  root.children[1] = argc % 3 ? &node1 : &node2;
  node1.children[0] = argc % 5 ? &node1 : &node2;
  node1.children[1] = argc % 7 ? &node1 : &node2;
  node2.children[0] = argc % 11 ? &node1 : &node2;
  node2.children[1] = argc % 13 ? &node1 : &node2;
  root.children[0]->children[1]->children[1]->children[0]->data = 1;
  assert(root.children[0]->children[1]->children[1]->children[0]->data == 1);
  assert(node1.data == argc);
}
