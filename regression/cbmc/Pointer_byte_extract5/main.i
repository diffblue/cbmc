void *malloc(__CPROVER_size_t);

typedef union
{
  int a;
  int b;
} Union;

#pragma pack(push)
#pragma pack(1)
typedef struct
{
  int Count;
  // flexible array member -- note that smt conversion does not yet support
  // 0-sized arrays
  Union List[0];
} Struct3;
#pragma pack(pop)

int main()
{
  Struct3 *p = malloc(sizeof(Struct3) + 2 * sizeof(Union));
  p->Count = 3;
  int po=0;

  // this should be fine
  p->List[0].a = 555;

  __CPROVER_assert(p->List[0].b==555, "p->List[0].b==555");
  __CPROVER_assert(p->List[0].a==555, "p->List[0].a==555");

  // this should be fine
  p->List[1].b = 999;

  __CPROVER_assert(p->List[1].b==999, "p->List[1].b==999");
  __CPROVER_assert(p->List[1].a==999, "p->List[1].a==999");

  // this is out-of-bounds
  p->List[2].a = 0;

  return 0;
}
