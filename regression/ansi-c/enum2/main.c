int main()
{
  enum { OP_FAST, OP_GLOBAL, OP_DEREF, OP_NAME } some_var;

  some_var=OP_GLOBAL;

  return 0;
}

// won't collide
enum { OP_NAME } other;
