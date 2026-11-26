typedef struct
{
  union {
    int access[256];
  };
} S1;

typedef struct
{
  int c;
} S2;

static S1(*const l[1]) = {((S1 *)((0x50000000UL) + 0x00000))};

void main()
{
#ifndef CMDLINE
  __CPROVER_allocated_memory(0x50000000UL, sizeof(S1));
#endif
  l[0]->access[0] = 0;
  __CPROVER_assert(l[0]->access[0] == 0, "holds");
  __CPROVER_assert(l[0]->access[1] == 0, "should fail");
#ifndef CMDLINE
  __CPROVER_allocated_memory(0x40000000UL + 0x40000, sizeof(S2));
#endif
  ((S2 *)((0x40000000UL) + 0x40000))->c = 0x0707;
}
