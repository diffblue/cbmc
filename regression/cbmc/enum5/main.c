enum en {
  e1
};

struct aStruct {
  enum en field;
};

void fun1(enum en *par)
{
  (*par) = e1;
}

int main()
{
  struct aStruct s;
  fun1(&s.field);
  __CPROVER_assert(0, "");
  return 0;
}
