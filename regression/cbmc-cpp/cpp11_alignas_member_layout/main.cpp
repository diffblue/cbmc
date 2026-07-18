// N5008 [dcl.align], [expr.sizeof]/2: alignas on a member raises the
// alignment requirement of the class, and sizeof includes the padding
// required to place such objects in an array; g++/clang give
// sizeof(membuft) == 4 and static_assert that at compile time.
//
// This used to fail (sizeof computed as 1): the C parser built the
// _Alignas(type) _Alignof-expression on a discarded parser-stack
// entry; the C++ parser lost the alignas merged into the declaration
// when rIntegralDeclaration installed the integral type; and the C++
// front end neither folded ID_C_alignment to a constant nor applied
// add_padding to explicitly-aligned structs.  This is the libstdc++
// __aligned_membuf pattern (_Rb_tree_node, _Hash_node storage).
//
// g++/clang++ accept and verify at runtime.
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
