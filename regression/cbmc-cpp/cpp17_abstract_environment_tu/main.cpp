// Dog-food reproducer: CBMC's own
// src/analyses/variable-sensitivity/abstract_environment.cpp (named on
// the options line) fails to convert.  UPDATE 2026-07-21 (evening):
// the original first error -- the static std::map<irep_idt, irep_idt>
// initializer routing a braced pair into the COMPARATOR parameter --
// no longer reproduces after the minimal-reproducer round's fixes;
// the TU now fails at "symbol 'shared_ptr' does not uniquely resolve"
// (shared_ptr.h:287 context, an untyped braced argument during an
// internal shared_ptr member's instantiation).  Isolated
// shared_ptr<const T> shapes (make_shared, copies, empty braced
// returns) convert CLEAN -- still context-dependent, so this test
// keeps naming the real source file.
// When THIS driver file is added as a second source, typechecking
// even SEGFAULTS (exit 139) while instantiating
// sharing_mapt<dstringt, shared_ptr<const abstract_objectt>, ...> ->
// sharing_nodet -> small_shared_n_way_ptrt::is_derived
// (util/sharing_node.h:187).
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int reached = 1;
  __CPROVER_assert(reached == 1, "abstract_environment converts");
  return 0;
}
