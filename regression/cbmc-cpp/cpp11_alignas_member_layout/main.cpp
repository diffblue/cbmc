// N5008 [dcl.align], [expr.sizeof]/2: alignas on a member raises the
// alignment requirement of the class, and sizeof includes the padding
// required to place such objects in an array; g++/clang give
// sizeof(membuft) == 4 and static_assert that at compile time.
//
// KNOWNBUG: CBMC's struct layout ignores the alignas specifier and
// computes sizeof(membuft) == 1.  This is the libstdc++
// __aligned_membuf pattern (_Rb_tree_node, _Hash_node storage): any
// container node built on aligned storage gets a wrong layout.  The
// same defect exists in C via _Alignas and in both languages via
// __attribute__((aligned(...))) on members.  Reduced by cvise from
// cpp20_map_basic's false positive (m[1] == 42 failing).
//
// g++/clang++ accept and verify at runtime.  Flip to CORE when fixed.
extern "C" void __CPROVER_assert(bool, const char *);

struct membuft
{
  alignas(int) char storage;
};

int main()
{
  __CPROVER_assert(
    sizeof(membuft) == sizeof(int), "alignas padding included in sizeof");
  membuft buf;
  int *p = reinterpret_cast<int *>(&buf.storage);
  *p = 42; // in-bounds for g++/clang (4-byte object)
  __CPROVER_assert(*p == 42, "store through aligned storage survives");
  return 0;
}
