/*******************************************************************\

Module: Dynamic frame condition checking

Author: Felipe R. Monteiro, felisous@amazon.com

\*******************************************************************/

/// \file
/// Summaries of the writes of the functions that DFCC does not instrument,
/// used by the loop assigns inference instead of their bodies.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_WRITE_SUMMARIES_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_WRITE_SUMMARIES_H

#include <util/irep.h>

#include <goto-programs/goto_functions.h>

#include <map>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

class namespacet;

/// The objects a pointer-valued expression of a function may point into,
/// flow-insensitively: globals, locals of the function (including its
/// parameter variables), the objects its parameters point to on entry, or
/// objects the analysis cannot name (`unknown`).
struct originst
{
  std::set<irep_idt> globals;
  std::set<irep_idt> locals;
  std::set<std::size_t> parameters;
  bool unknown = false;

  /// Add \p other to this. Returns true if this changed.
  bool merge(const originst &other);

  bool operator==(const originst &other) const
  {
    return globals == other.globals && locals == other.locals &&
           parameters == other.parameters && unknown == other.unknown;
  }
};

/// What a function, its callees included, may write outside its own locals,
/// and what its result may point to.
struct write_summaryt
{
  /// Globals it may write, whole.
  std::set<irep_idt> globals;
  /// Parameters through which it may write, into the whole object they point
  /// to on entry.
  std::set<std::size_t> parameters;
  /// It may write through a pointer whose target the analysis cannot name.
  bool unknown = false;
  originst result;

  bool operator==(const write_summaryt &other) const
  {
    return globals == other.globals && parameters == other.parameters &&
           unknown == other.unknown && result == other.result;
  }
};

/// Computes `write_summaryt`s, flow-insensitively, over the bodies in a
/// `goto_functionst`.
class write_summariest
{
public:
  write_summariest(const goto_functionst &goto_functions, const namespacet &ns)
    : goto_functions(goto_functions), ns(ns)
  {
  }

  /// The summaries of \p roots and of every function they call, transitively.
  void compute(const std::vector<irep_idt> &roots);

  /// The summary of \p id, which `compute` must have been called for.
  const write_summaryt &operator[](const irep_idt &id)
  {
    return summaries[id];
  }

  /// Whether a value of \p type contains pointers.
  bool has_pointers(const typet &type);

private:
  const goto_functionst &goto_functions;
  const namespacet &ns;
  std::vector<irep_idt> functions;
  std::map<irep_idt, write_summaryt> summaries;
  std::unordered_map<typet, bool, irep_hash> pointer_types;

  // State of the function being analyzed.
  std::map<irep_idt, originst> variables;
  write_summaryt current;
  bool variables_changed = false;

  bool has_body(const irep_idt &id) const;
  const goto_programt &body_of(const irep_idt &id) const;
  bool is_global(const irep_idt &id) const;

  write_summaryt analyze(const irep_idt &id);
  void analyze(const goto_programt::instructiont &instruction);
  void call(const goto_programt::instructiont &instruction);

  /// Records that \p content may be written into the objects of \p target.
  void write_through(const originst &target, const originst &content);

  /// Records an assignment of \p content to \p lhs.
  void write(const exprt &lhs, const originst &content);

  /// The objects whose address is `&object`.
  originst object_origins(const exprt &object);

  /// The objects the pointers in the value of \p expr may point into.
  originst origins(const exprt &expr);
};

/// While it lives, replaces the body of each function that DFCC does not
/// instrument (`dfcc_is_cprover_function_symbol`) by a summary of its writes,
/// so that inlining it into the copy that the inference works on is cheap:
/// a tool may instrument every instruction of a loop with calls to such
/// functions (for example Kani's aliasing checks), and inlining their bodies
/// can then run out of memory. Their writes are not checked against a write
/// set, but the objects they write must still be havocked, so the summary
/// writes a nondeterministic value to:
/// - each global the function or its callees may write, whole;
/// - the whole object each pointer parameter it may write through points to;
/// - its result, which may point to the objects its result may point to.
/// A function that may write through a pointer the summary cannot name keeps
/// its body. The bodies are restored on destruction.
class write_summary_bodiest
{
public:
  /// Replaces the bodies of the functions DFCC does not instrument that
  /// \p program may call, directly or through the functions it calls.
  /// Only those can be inlined into \p program, and summarizing every
  /// function of a large program, for every function with loops, is costly.
  write_summary_bodiest(
    goto_functionst &goto_functions,
    const goto_programt &program,
    const namespacet &ns);

  ~write_summary_bodiest();

  write_summary_bodiest(const write_summary_bodiest &) = delete;
  write_summary_bodiest &operator=(const write_summary_bodiest &) = delete;

private:
  goto_functionst &goto_functions;
  std::vector<std::pair<irep_idt, goto_programt>> saved;
};

#endif
