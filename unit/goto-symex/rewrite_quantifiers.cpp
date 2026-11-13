/*******************************************************************\

Module: Unit tests for goto_symext::rewrite_quantifiers

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for goto_symext::rewrite_quantifiers handling of bound variables
/// that are plain symbols rather than SSA expressions. Such bound variables are
/// not produced by the C front end (which renames them to SSA expressions
/// before rewriting), but can be presented by other front ends. The rewriting
/// must not assume the bound variable is an SSA expression.

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/options.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_function.h>
#include <goto-programs/goto_program.h>

#include <ansi-c/ansi_c_language.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/path_storage.h>
#include <goto-symex/symex_target_equation.h>
#include <langapi/mode.h>
#include <testing-utils/use_catch.h>

/// Subclass exposing the protected \ref goto_symext::rewrite_quantifiers method
/// so that it can be exercised directly.
class test_goto_symext : public goto_symext
{
public:
  using goto_symext::goto_symext;
  using goto_symext::rewrite_quantifiers;
};

/// Run rewrite_quantifiers on \p quantifier in a minimal symex state whose
/// current instruction is an assertion (when \p as_assertion is true) or an
/// assumption (otherwise). The bound-variable symbol \p bound_variable is added
/// to the symbol table so that it can be declared during rewriting.
static exprt run_rewrite_quantifiers(
  const bool as_assertion,
  exprt quantifier,
  const symbol_exprt &bound_variable)
{
  // shadow-memory initialisation during symex_decl looks up the symbol's
  // language; register the C language so that lookup succeeds. Register it
  // only once: register_language does an unconditional push_back onto the
  // global language list, and this helper runs once per WHEN section.
  static const bool language_registered = []()
  {
    register_language(new_ansi_c_language);
    return true;
  }();
  (void)language_registered;

  symbol_tablet symbol_table;
  symbolt bound_symbol{
    bound_variable.identifier(), bound_variable.type(), ID_C};
  symbol_table.insert(bound_symbol);

  // A goto program with a single assertion or assumption that the symex state's
  // program counter will point at.
  goto_programt goto_program;
  if(as_assertion)
    goto_program.add(
      goto_programt::make_assertion(true_exprt{}, source_locationt{}));
  else
    goto_program.add(
      goto_programt::make_assumption(true_exprt{}, source_locationt{}));
  goto_program.add(goto_programt::make_end_function());
  goto_program.compute_location_numbers();

  null_message_handlert message_handler;
  optionst options;
  symex_target_equationt equation{message_handler};
  path_fifot path_storage;
  // symex_decl (reached via rewrite_quantifiers) queries whether the declared
  // object is 'dirty', so the dirty analysis must be initialised.
  goto_functiont empty_function;
  path_storage.dirty.populate_dirty_for_function("fun", empty_function);
  guard_managert guard_manager;

  test_goto_symext symex{
    message_handler,
    symbol_table,
    equation,
    options,
    path_storage,
    guard_manager};

  symex_targett::sourcet source{"fun", goto_program.instructions.begin()};
  std::size_t fresh_name_count = 1;
  auto fresh_name = [&fresh_name_count](const irep_idt &)
  { return fresh_name_count++; };
  goto_symex_statet state{
    source,
    DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE,
    false, // should_simplify: disabled to keep the state minimal
    irep_idt{},
    guard_manager,
    fresh_name};

  symex.rewrite_quantifiers(quantifier, state);
  return quantifier;
}

SCENARIO(
  "rewrite_quantifiers handles plain-symbol bound variables",
  "[core][goto-symex][rewrite_quantifiers]")
{
  // Put invariants into throwing mode for this scenario. Without the
  // is_ssa_expr guard in rewrite_quantifiers, to_ssa_expr fails via
  // ssa_exprt::check with validation_modet::INVARIANT, which aborts the unit
  // binary by default; throwing mode turns that into a thrown exception that
  // the REQUIRE_NOTHROW checks below can report as a clean test failure.
  const cbmc_invariants_should_throwt invariants_throw;

  const signedbv_typet int_type{32};
  // A bound variable that is a plain symbol, not an SSA expression. This models
  // what front ends other than C (e.g. Strata) may present to symex.
  const symbol_exprt bound_variable{"x", int_type};
  const exprt body = equal_exprt{bound_variable, from_integer(0, int_type)};

  GIVEN("a universal quantifier with a plain-symbol bound variable")
  {
    const forall_exprt quantifier{bound_variable, body};

    WHEN("rewrite_quantifiers is applied in an assertion")
    {
      THEN("it does not fail and replaces the quantifier by its body")
      {
        exprt result;
        REQUIRE_NOTHROW(
          result = run_rewrite_quantifiers(true, quantifier, bound_variable));
        REQUIRE(result.id() != ID_forall);
        REQUIRE(result == body);
      }
    }
  }

  GIVEN("an existential quantifier with a plain-symbol bound variable")
  {
    const exists_exprt quantifier{bound_variable, body};

    WHEN("rewrite_quantifiers is applied in an assumption")
    {
      THEN("it does not fail and replaces the quantifier by its body")
      {
        exprt result;
        REQUIRE_NOTHROW(
          result = run_rewrite_quantifiers(false, quantifier, bound_variable));
        REQUIRE(result.id() != ID_exists);
        REQUIRE(result == body);
      }
    }
  }
}
