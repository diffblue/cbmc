// A variadic function template forwarding its pack to clang's
// __builtin_operator_new -- libc++'s __libcpp_operator_new shape
// (<new>).  The builtin has no findable declaration, so the instance
// body failed to convert and every allocation through it returned a
// nondet pointer (the root under std::set/std::map node allocation).
// Per clang's documentation the builtin behaves exactly like a call
// to ::operator new ([new.delete.single]: non-null storage of the
// requested size, or a throw).  clang++-only shape (-w for the
// builtin at non-constant size).
extern "C" void __CPROVER_assert(bool, const char *);

struct node
{
  int v;
};

template <class... A>
void *op_new(A... a)
{
  return __builtin_operator_new(a...);
}

long sz = sizeof(struct node);

node *alloc()
{
  void *p = op_new(sz);
  return static_cast<node *>(p);
}

node *g_n = alloc();

int main()
{
  g_n->v = 7;
  __CPROVER_assert(g_n->v == 7, "variadic builtin new");
}
