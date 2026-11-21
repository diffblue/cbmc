#define BLOCK_SIZE 128

int main()
{
  unsigned n;

  unsigned block_count = n / BLOCK_SIZE;

  for(unsigned i = 0; i < block_count; i++)
    // clang-format off
    __CPROVER_loop_invariant(block_count == n / BLOCK_SIZE)
  {
    __CPROVER_assert(i * BLOCK_SIZE < n, "property 1");
    __CPROVER_assert(i * BLOCK_SIZE + BLOCK_SIZE - 1 < n, "property 2");
  }
  // clang-format on
}
