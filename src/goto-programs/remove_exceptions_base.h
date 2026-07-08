/*******************************************************************\

Module: Remove exceptions (language-agnostic goto-level lowering)

Author: Cristina David (Java), Kiro (base extraction)

\*******************************************************************/

/// \file
/// Language-agnostic base for lowering exceptions (CATCH-PUSH / CATCH-POP /
/// CATCH-landingpad / THROW) to ordinary control flow (GOTOs and assignments),
/// so that goto-symex need not model exceptions.
///
/// The pass structure -- tracking the stack of active catch clauses, emitting
/// the per-handler dispatch sequence after a THROW or a possibly-throwing
/// FUNCTION_CALL, propagating an escaped exception to the end of the function,
/// and recomputing DEAD ranges -- is shared.  The language-specific pieces are
/// provided by virtual hooks: the in-flight exception global, the per-handler
/// match guard, how a THROW sets the in-flight exception, and how a handler
/// binds/clears it.  JBMC (Java, instanceof matching, reference exceptions) and
/// the C++ front-end (cpp_exception_id matching, value exceptions) derive from
/// this base.

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_EXCEPTIONS_BASE_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_EXCEPTIONS_BASE_H

#include <goto-programs/goto_program.h>

#include <functional>
#include <set>
#include <vector>

class goto_functionst;
class message_handlert;
class symbol_table_baset;

class remove_exceptions_baset
{
public:
  typedef std::function<bool(const irep_idt &)> function_may_throwt;

  remove_exceptions_baset(
    symbol_table_baset &_symbol_table,
    function_may_throwt _function_may_throw,
    message_handlert &_message_handler)
    : symbol_table(_symbol_table),
      function_may_throw(std::move(_function_may_throw)),
      message_handler(_message_handler)
  {
  }

  virtual ~remove_exceptions_baset() = default;

  void operator()(goto_functionst &goto_functions);
  void
  operator()(const irep_idt &function_identifier, goto_programt &goto_program);

protected:
  symbol_table_baset &symbol_table;
  function_may_throwt function_may_throw;
  message_handlert &message_handler;

  typedef std::vector<std::pair<irep_idt, goto_programt::targett>>
    catch_handlerst;
  typedef std::vector<catch_handlerst> stack_catcht;

  enum class instrumentation_resultt
  {
    DID_NOTHING,
    ADDED_CODE_WITHOUT_MAY_THROW,
    ADDED_CODE_WITH_MAY_THROW,
  };

  // -- language-specific hooks --

  /// The global that carries an in-flight exception (null / absent when none).
  virtual symbol_exprt get_inflight_exception_global() = 0;

  /// Guard that holds when there is no in-flight exception.
  virtual exprt no_inflight_exception() = 0;

  /// Insert, immediately after \p instr_it, a conditional GOTO to
  /// \p handler_target taken when the in-flight exception matches a handler
  /// catching \p tag (base classes included, as the language sees fit).  This
  /// is a hook because matching is language-specific (Java instanceof vs C++
  /// cpp_exception_id).  Only called for non-universal (non-empty-tag)
  /// handlers; catch(...) is handled by the base as the default target.
  virtual void add_handler_dispatch(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const irep_idt &tag,
    const goto_programt::targett &handler_target) = 0;

  /// Turn the THROW at \p instr_it into code that records the thrown value as
  /// the in-flight exception (leaving control flow to the dispatch sequence
  /// inserted before it).
  virtual void set_inflight_exception(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it) = 0;

  /// Bind a caught exception to a handler landing pad (a CATCH landingpad
  /// instruction) and clear the in-flight exception.  Languages without an
  /// explicit landing-pad instruction leave this empty and use prepare_handler.
  virtual void instrument_exception_handler(
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    bool may_catch) = 0;

  /// Called once per distinct handler target when a dispatch to it is first
  /// emitted, before the goto is inserted.  Languages that bind the handler
  /// parameter at the handler entry (rather than via a landing-pad
  /// instruction) do so here.  Default: nothing.
  virtual void prepare_handler(
    goto_programt &goto_program,
    const goto_programt::targett &handler)
  {
    (void)goto_program;
    (void)handler;
  }

  // -- shared implementation --

  bool function_or_callees_may_throw(const goto_programt &) const;

  goto_programt::targett find_universal_exception(
    const stack_catcht &stack_catch,
    goto_programt &goto_program,
    std::size_t &universal_try,
    std::size_t &universal_catch);

  void add_exception_dispatch_sequence(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &instr_it,
    const stack_catcht &stack_catch,
    const std::vector<symbol_exprt> &locals);

  bool instrument_throw(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &,
    const stack_catcht &,
    const std::vector<symbol_exprt> &);

  instrumentation_resultt instrument_function_call(
    const irep_idt &function_identifier,
    goto_programt &goto_program,
    const goto_programt::targett &,
    const stack_catcht &,
    const std::vector<symbol_exprt> &);

  void instrument_exceptions(
    const irep_idt &function_identifier,
    goto_programt &goto_program);

  // handler targets already prepared (prepare_handler called), to do it once
  std::set<const goto_programt::instructiont *> prepared_handlers;
};

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_EXCEPTIONS_BASE_H
