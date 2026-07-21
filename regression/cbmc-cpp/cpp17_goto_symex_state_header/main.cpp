// Dog-food reproducer: CBMC's own <goto-symex/goto_symex_state.h>
// fails to convert.  Two visible symptoms, likely one root:
//  * "found no match for symbol 'symbol_exprt'" with an EMPTY argument
//    list -- something value-initializes a symbol_exprt (the class has
//    no default constructor by design; suspicion: sharing_mapt<exprt,
//    symbol_exprt> machinery or a synthesized member init);
//  * "member 'goto_statet::goto_statet(this)' is not accessible" --
//    the DELETED default constructor ([dcl.fct.def.delete]) is
//    demanded by CBMC-synthesized code although the source never
//    default-constructs a goto_statet.
// Downstream this leaves path_storaget::patht sizeless ("type has no
// size" at __aligned_buffer), blocking symex_dereference.cpp,
// change_impact.cpp and every other TU including path_storage.h.
// Isolated shapes (deleted-default-ctor + defaulted copy;
// sharing_mapt<exprt, symbol_exprt> alone) all pass -- the trigger
// needs this TU's context, so this test keeps the include.
#include <goto-symex/goto_symex_state.h>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int reached = 1;
  __CPROVER_assert(reached == 1, "goto_symex_state.h converts");
  return 0;
}
