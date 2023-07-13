inline int memcmp(const char *s1, const char *s2, unsigned n)
{
  int res = 0;
  const unsigned char *sc1 = s1, *sc2 = s2;
  for(; n != 0; n--)
    // clang-format off
    __CPROVER_loop_invariant(n <= __CPROVER_loop_entry(n))
    __CPROVER_loop_invariant(__CPROVER_same_object(sc1, __CPROVER_loop_entry(sc1)))
    __CPROVER_loop_invariant(__CPROVER_same_object(sc2, __CPROVER_loop_entry(sc2)))
    __CPROVER_loop_invariant(sc1 <= s1 + __CPROVER_loop_entry(n))
    __CPROVER_loop_invariant(sc2 <= s2 + __CPROVER_loop_entry(n))
    __CPROVER_loop_invariant(res == 0)
    __CPROVER_loop_invariant(sc1 -(const unsigned char*)s1 == sc2 -(const unsigned char*)s2
      &&  sc1 -(const unsigned char*)s1== __CPROVER_loop_entry(n) - n)
    // clang-format on
    {
      res = (*sc1++) - (*sc2++);
      long d1 = sc1 - (const unsigned char *)s1;
      long d2 = sc2 - (const unsigned char *)s2;
      if(res != 0)
        return res;
    }
  return res;
}

int main()
{
  unsigned SIZE;
  __CPROVER_assume(1 < SIZE && SIZE < 65536);
  unsigned char *a = malloc(SIZE);
  unsigned char *b = malloc(SIZE);
  memcpy(b, a, SIZE);
  assert(memcmp(a, b, SIZE) == 0);
}
