struct S1
{
  char a;
  struct
  {
    short b;
  } c;
};

#pragma pack(4)
// note that the above is different from __attribute__((packed, aligned(4))) in
// that it sets the _maximum_ alignment of members - it does not affect the
// overall alignment of the struct

struct S2
{
  char a;
  struct
  {
    short b;
  } c;
};

int main()
{
  _Static_assert(sizeof(struct S1) == sizeof(struct S2), "");
}
