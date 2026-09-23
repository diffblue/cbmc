typedef __CPROVER_size_t size_t;

void returns_a_range(const char *base, size_t size, size_t *pos)
  // clang-format off
  __CPROVER_requires(__CPROVER_r_ok(base, size))
  __CPROVER_requires(__CPROVER_rw_ok(pos))
  __CPROVER_requires(*pos <= size)
  __CPROVER_assigns(*pos)
  __CPROVER_ensures(*pos <= size)
// clang-format on
{
  size_t p = *pos;

  // skip a pair of double quotes
  if(p < size && base[p] == '"')
  {
    p++;

    if(p < size && base[p] == '"')
    {
      p++;
      *pos = p;
    }
  }
}
