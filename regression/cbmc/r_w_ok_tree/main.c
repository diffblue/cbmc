struct tree_node
{
  int value;
  struct tree_node *left;
  struct tree_node *right;
};

// rw_ok on a tree-shaped recursive struct lets us traverse both child
// pointers; the lazily-created auto-objects bound the tree by --unwind so the
// traversal terminates without spurious failures.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  struct tree_node *root;
  __CPROVER_assume(__CPROVER_rw_ok(root, sizeof(*root)));
  __CPROVER_assume(root != 0);

  struct tree_node *l = root->left;
  struct tree_node *r = root->right;
  if(l != 0)
  {
    struct tree_node *ll = l->left;
    (void)ll;
  }
  if(r != 0)
  {
    struct tree_node *rr = r->right;
    (void)rr;
  }
  __CPROVER_assert(1, "traversal terminates");
  return 0;
}
