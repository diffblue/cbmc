// Reduced (2026-07-22, from #include <goto-symex/goto_symex_state.h>)
// to the goto_symex_statet SHAPE that still fails: a final class
// deriving from goto_statet, with a std::vector of a guardt-holding
// struct and a DEFAULTED copy constructor.  CBMC reports "found no
// match for symbol 'symbol_exprt'" with EMPTY argument types (a
// demanded default-construction; symbol_exprt has no default
// constructor) plus "goto_statet::goto_statet(this) is not
// accessible" -- the synthesized copy machinery demands members
// deleted or inaccessible in the real classes ([class.copy.ctor],
// [dcl.fct.def.default]: a defaulted copy constructor must use the
// bases'/members' copy constructors, not default constructions).
// Related root ingredient captured std-only in
// cpp17_vector_emplace_nondefault_pair (pair with a
// non-default-constructible member under emplace forwarding).
// g++ and clang++ accept this TU.
#include <util/invariant.h>
#include <util/ssa_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <analyses/guard.h>

#include <goto-symex/call_stack.h>
#include <goto-symex/field_sensitivity.h>
#include <goto-symex/goto_state.h>
#include <goto-symex/renaming_level.h>
#include <goto-symex/shadow_memory_state.h>

#include <functional>
#include <unordered_map>

class incremental_dirtyt;
class symex_target_equationt;

class goto_symex_statet final : public goto_statet
{
public:
  goto_symex_statet(
    const symex_targett::sourcet &,
    std::size_t max_field_sensitive_array_size,
    bool should_simplify,
    const irep_idt language_mode,
    guard_managert &manager,
    std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider);
  ~goto_symex_statet();

  // Manager is required to be able to resize the thread vector
  guard_managert &guard_manager;
  symex_target_equationt *symex_target = nullptr;

  struct threadt
  {
    goto_programt::const_targett pc;
    irep_idt function_id;
    guardt guard;
    call_stackt call_stack;
    std::map<irep_idt, unsigned> function_frame;
    unsigned atomic_section_id = 0;
    explicit threadt(guard_managert &guard_manager)
      : guard(true_exprt(), guard_manager)
    {
    }
  };

  std::vector<threadt> threads;

  /// \brief Dangerous, do not use
  ///
  /// Copying a state S1 to S2 risks S2 pointing to a deallocated
  /// symex_target_equationt if S1 (and the symex_target_equationt that its
  /// `symex_target` member points to) go out of scope. If your class has a
  /// goto_symex_statet member and needs a copy constructor, copy instances
  /// of this class using the public two-argument copy constructor
  /// constructor to ensure that the copy points to an allocated
  /// symex_target_equationt. The two-argument copy constructor uses this
  /// private copy constructor as a delegate.
  goto_symex_statet(const goto_symex_statet &other) = default;
};
int main() { return 0; }
