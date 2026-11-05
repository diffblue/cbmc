#pragma pack(push, 1)
struct A
{
  char c;
  int i;
};
#pragma pack(pop)

#pragma pack(push, 2)
struct B
{
  char c;
  long long ll;
};
#pragma pack(pop)

struct C
{
  char c;
  int i;
};

struct A a;
struct B b;
struct C c;

int main()
{
  __CPROVER_assert(sizeof(a) == 5, "A is packed");
  __CPROVER_assert(sizeof(b) == 10, "B has 2-byte alignment");
  __CPROVER_assert(sizeof(c) == 8, "C is not packed");
  return 0;
}
