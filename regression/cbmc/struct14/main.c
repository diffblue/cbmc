struct S
{
  int x;
};

int main(int argc, char *argv[])
{
  struct S s;

  if(argc > 3)
    s.x = 42;

  __CPROVER_assert(s.x == 42, "should fail");
}
