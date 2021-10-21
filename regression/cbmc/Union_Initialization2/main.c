union U {
};

struct S
{
  int a;
  union U u;
  int b;
} s;

int main()
{
  __CPROVER_assert(0, "");
}
