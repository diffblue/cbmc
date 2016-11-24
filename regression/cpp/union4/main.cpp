struct A
{
  // 'a' is a duplicate
  union {int a;};
  char a;
};

