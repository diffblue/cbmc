/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H

#include <iosfwd>
#include <vector>

#include <util/message.h>
#include <util/options.h>

#include <goto-programs/goto_program.h>

class merge_irept;

/// Step of the trace of a GOTO program
///
/// A step is either:
///   - an assignment
///   - an assume statement
///   - an assertion
///   - a goto instruction
///   - a constraint (unused)
///   - a function call
///   - a function return
///   - a location (unused)
///   - an output
///   - an input
///   - a declaration
///   - a dead statement
///   - a shared read (unused)
///   - a shared write (unused)
///   - a spawn statement
///   - a memory barrier
///   - an atomic begin (unused)
///   - an atomic end (unused)
/// \ingroup gr_goto_symex
class goto_trace_stept
{
public:
  /// Number of the step in the trace
  std::size_t step_nr;

  bool is_assignment() const      { return type==typet::ASSIGNMENT; }
  bool is_assume() const          { return type==typet::ASSUME; }
  bool is_assert() const          { return type==typet::ASSERT; }
  bool is_goto() const            { return type==typet::GOTO; }
  bool is_constraint() const      { return type==typet::CONSTRAINT; }
  bool is_function_call() const   { return type==typet::FUNCTION_CALL; }
  bool is_function_return() const { return type==typet::FUNCTION_RETURN; }
  bool is_location() const        { return type==typet::LOCATION; }
  bool is_output() const          { return type==typet::OUTPUT; }
  bool is_input() const           { return type==typet::INPUT; }
  bool is_decl() const            { return type==typet::DECL; }
  bool is_dead() const            { return type==typet::DEAD; }
  bool is_shared_read() const     { return type==typet::SHARED_READ; }
  bool is_shared_write() const    { return type==typet::SHARED_WRITE; }
  bool is_spawn() const           { return type==typet::SPAWN; }
  bool is_memory_barrier() const  { return type==typet::MEMORY_BARRIER; }
  bool is_atomic_begin() const    { return type==typet::ATOMIC_BEGIN; }
  bool is_atomic_end() const      { return type==typet::ATOMIC_END; }

  enum class typet
  {
    NONE,
    ASSIGNMENT,
    ASSUME,
    ASSERT,
    GOTO,
    LOCATION,
    INPUT,
    OUTPUT,
    DECL,
    DEAD,
    FUNCTION_CALL,
    FUNCTION_RETURN,
    CONSTRAINT,
    SHARED_READ,
    SHARED_WRITE,
    SPAWN,
    MEMORY_BARRIER,
    ATOMIC_BEGIN,
    ATOMIC_END
  };

  typet type;

  // we may choose to hide a step
  bool hidden;

  // this is related to an internal expression
  bool internal;

  // we categorize
  enum class assignment_typet { STATE, ACTUAL_PARAMETER };
  assignment_typet assignment_type;

  // The instruction that created this step
  // (function calls are in the caller, function returns are in the callee)
  irep_idt function_id;
  goto_programt::const_targett pc;

  // this transition done by given thread number
  unsigned thread_nr;

  // for assume, assert, goto
  bool cond_value;
  exprt cond_expr;

  // for assert
  irep_idt property_id;
  std::string comment;

  // the full, original lhs expression, after dereferencing
  exprt full_lhs;

  // the object being assigned
  optionalt<symbol_exprt> get_lhs_object() const;

  // A constant with the new value of the lhs
  exprt full_lhs_value;

  // for INPUT/OUTPUT
  irep_idt format_string, io_id;
  typedef std::list<exprt> io_argst;
  io_argst io_args;
  bool formatted;

  // for function calls
  irep_idt called_function;

  // for function call
  std::vector<exprt> function_arguments;

  /// Outputs the trace step in ASCII to a given stream
  void output(
    const class namespacet &ns,
    std::ostream &out) const;

  goto_trace_stept():
    step_nr(0),
    type(typet::NONE),
    hidden(false),
    internal(false),
    assignment_type(assignment_typet::STATE),
    thread_nr(0),
    cond_value(false),
    formatted(false)
  {
    full_lhs.make_nil();
    full_lhs_value.make_nil();
    cond_expr.make_nil();
  }

  /// Use \p dest to establish sharing among ireps.
  /// \param [out] dest: irep storage container.
  void merge_ireps(merge_irept &dest);
};

/// Trace of a GOTO program.
/// This is a wrapper for a list of steps.
/// \ingroup gr_goto_symex
class goto_tracet
{
public:
  typedef std::list<goto_trace_stept> stepst;
  stepst steps;

  void clear()
  {
    steps.clear();
  }

  /// Outputs the trace in ASCII to a given stream
  void output(
    const class namespacet &ns,
    std::ostream &out) const;

  void swap(goto_tracet &other)
  {
    other.steps.swap(steps);
  }

  /// Add a step at the end of the trace
  void add_step(const goto_trace_stept &step)
  {
    steps.push_back(step);
  }

  /// Retrieves the final step in the trace for manipulation
  /// (used to fill a trace from code, hence non-const)
  goto_trace_stept &get_last_step()
  {
    return steps.back();
  }

  const goto_trace_stept &get_last_step() const
  {
    return steps.back();
  }

  /// Returns the property IDs of all failed assertions in the trace
  std::set<irep_idt> get_failed_property_ids() const;
};

/// Options for printing the trace using show_goto_trace
struct trace_optionst
{
  /// Add rawLhs property to trace
  bool json_full_lhs;
  /// Represent plain trace values in hex
  bool hex_representation;
  /// Use prefix (`0b` or `0x`) for distinguishing the base of the
  /// representation.
  bool base_prefix;
  /// Show function calls in plain text trace
  bool show_function_calls;
  /// Show original code in plain text trace
  bool show_code;
  /// Give a compact trace
  bool compact_trace;
  /// Give a stack trace only
  bool stack_trace;

  static const trace_optionst default_options;

  explicit trace_optionst(const optionst &options)
  {
    json_full_lhs = options.get_bool_option("trace-json-extended");
    hex_representation = options.get_bool_option("trace-hex");
    base_prefix = hex_representation;
    show_function_calls = options.get_bool_option("trace-show-function-calls");
    show_code = options.get_bool_option("trace-show-code");
    compact_trace = options.get_bool_option("compact-trace");
    stack_trace = options.get_bool_option("stack-trace");
  };

private:
  trace_optionst()
  {
    json_full_lhs = false;
    hex_representation = false;
    base_prefix = false;
    show_function_calls = false;
    show_code = false;
    compact_trace = false;
    stack_trace = false;
  };
};

/// Output the trace on the given stream \p out
void show_goto_trace(
  messaget::mstreamt &out,
  const namespacet &ns,
  const goto_tracet &goto_trace,
  const trace_optionst &trace_options = trace_optionst::default_options);

#define OPT_GOTO_TRACE                                                         \
  "(trace-json-extended)"                                                      \
  "(trace-show-function-calls)"                                                \
  "(trace-show-code)"                                                          \
  "(trace-hex)"                                                                \
  "(compact-trace)"                                                            \
  "(stack-trace)"

#define HELP_GOTO_TRACE                                                        \
  " --trace-json-extended        add rawLhs property to trace\n"               \
  " --trace-show-function-calls  show function calls in plain trace\n"         \
  " --trace-show-code            show original code in plain trace\n"          \
  " --trace-hex                  represent plain trace values in hex\n"        \
  " --compact-trace              give a compact trace\n"                       \
  " --stack-trace                give a stack trace only\n"

#define PARSE_OPTIONS_GOTO_TRACE(cmdline, options)                             \
  if(cmdline.isset("trace-json-extended"))                                     \
    options.set_option("trace-json-extended", true);                           \
  if(cmdline.isset("trace-show-function-calls"))                               \
    options.set_option("trace-show-function-calls", true);                     \
  if(cmdline.isset("trace-show-code"))                                         \
    options.set_option("trace-show-code", true);                               \
  if(cmdline.isset("trace-hex"))                                               \
    options.set_option("trace-hex", true);                                     \
  if(cmdline.isset("compact-trace"))                                           \
    options.set_option("compact-trace", true);                                 \
  if(cmdline.isset("stack-trace"))                                             \
    options.set_option("stack-trace", true);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H
