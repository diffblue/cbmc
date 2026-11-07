// Test that self-referential struct types do not cause infinite
// recursion in size_of_expr. A struct containing a pointer to itself
// is common in C++ (e.g., linked list nodes, iterators).
struct Node
{
  int value;
  Node *next;
};

int main()
{
  Node n;
  n.value = 42;
  n.next = 0;
  return 0;
}
