typedef __CPROVER_size_t size_t;

void returns_a_range(const char *base, size_t size, size_t pos, size_t *length)
  // clang-format off
  __CPROVER_requires(__CPROVER_r_ok(base, size))
  __CPROVER_requires(pos <= size)
  __CPROVER_requires(__CPROVER_rw_ok(length))
  __CPROVER_assigns(*length)
  __CPROVER_ensures(__CPROVER_old(pos) + *length <= size)
// clang-format on
{
  // skip a pair of double quotes
  size_t start = pos;

  if(pos < size && base[pos] == '"')
  {
    pos++;

    if(pos < size && base[pos] == '"')
      pos++;
  }

  *length = pos - start;
}
