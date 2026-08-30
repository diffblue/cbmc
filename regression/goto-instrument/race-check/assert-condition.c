int shared;

void writer(void)
{
  shared = 42;
}

int main(void)
{
__CPROVER_ASYNC_0:
  writer();
  // Shared read inside an ASSERT condition (exercises the is_assert() path).
  // The user assertion itself always holds (shared is 0 or 42); the race
  // assertion inserted before it is what fails.
  __CPROVER_assert(shared >= 0, "shared is non-negative");
  return 0;
}
