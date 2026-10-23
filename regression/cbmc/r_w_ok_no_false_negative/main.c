// Verify that nondet pointers WITHOUT rw_ok still fail pointer checks.
// The auto-object mechanism must not mask genuine memory-safety errors.
struct node
{
  int data;
  struct node *next;
};

int main()
{
  struct node *p; // nondet pointer, NO rw_ok
  if(p != 0)
  {
    if(p->next != 0)
    {
      int x = p->next->data; // must fail pointer checks
    }
  }
}
