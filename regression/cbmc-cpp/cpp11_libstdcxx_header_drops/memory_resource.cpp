#include <memory_resource>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::pmr::pool_options o{};
  __CPROVER_assert(o.max_blocks_per_chunk == 0, "pool_options");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
