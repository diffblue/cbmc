// Anonymous aggregates with the same members are only the same type when
// their layout attributes agree as well.

struct
{
  int i;
} a1;
struct
{
  int i;
} __attribute__((packed)) a2;
struct
{
  int i;
} __attribute__((aligned(8))) a3;
struct
{
  int i __attribute__((aligned(16)));
} a4;

_Static_assert(__alignof__(a1) == 4, "");
_Static_assert(__alignof__(a2) == 1, "");
_Static_assert(__alignof__(a3) == 8, "");
_Static_assert(__alignof__(a4) == 16, "");

int main()
{
  return 0;
}
