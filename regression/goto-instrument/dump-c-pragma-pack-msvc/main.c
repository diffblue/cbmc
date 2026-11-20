// Visual Studio uses the #pragma pack in effect at each member, and caps the
// trailing padding at the one in effect at the end of the definition
#pragma pack(push, 1)
struct V
{
  char c;
  int i;
#pragma pack(4)
  int j;
  char e;
#pragma pack(2)
};
#pragma pack(pop)

struct V v;

int main()
{
  __CPROVER_assert((char *)&v.i - (char *)&v == 1, "i is packed");
  __CPROVER_assert((char *)&v.j - (char *)&v == 8, "j is aligned to 4");
  __CPROVER_assert(sizeof(struct V) == 14, "trailing padding up to 2");
  return 0;
}
