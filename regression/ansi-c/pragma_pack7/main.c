// Visual Studio applies the #pragma pack in effect at each member, also when
// it changes within the definition of an aggregate.

struct C1
{
  char c;
#pragma pack(push, 1)
  int i;
#pragma pack(pop)
};

#pragma pack(push, 1)
struct C2
{
  char c;
#pragma pack(pop)
  int i;
#pragma pack(push, 1)
};
#pragma pack(pop)

#pragma pack(push, 2)
struct C3
{
  char c;
  long long ll;
  struct
  {
    long long x;
  } s;
};
#pragma pack(pop)

_Static_assert(sizeof(struct C1) == 5, "");
_Static_assert(sizeof(struct C2) == 8, "");
_Static_assert(sizeof(struct C3) == 18, "");
_Static_assert(__alignof(struct C3) == 2, "");

int main()
{
  return 0;
}
