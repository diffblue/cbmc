#define C 8

typedef unsigned st[C];

// clang-format off
void init_st(st dst)
  __CPROVER_requires(__CPROVER_is_fresh(dst, sizeof(st)))
  __CPROVER_assigns(__CPROVER_object_whole(dst))
  __CPROVER_ensures(__CPROVER_forall {
    unsigned i; (0 <= i && i < C) ==> dst[i] == 0
  });
// clang-format on

void init_st(st dst)
{
  __CPROVER_size_t i;
  for(i = 0; i < C; i++)
  {
    dst[i] = 0;
  }
}

int main()
{
  st dest;

  init_st(dest);
}
