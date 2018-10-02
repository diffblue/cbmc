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

#include <util/namespace.h>
#include <util/options.h>
#include <util/ssa_expr.h>

#include <goto-programs/goto_program.h>

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_trace_stept
{
public:
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

  goto_programt::const_targett pc;

  // this transition done by given thread number
  unsigned thread_nr;

  // for assume, assert, goto
  bool cond_value;
  exprt cond_expr;

  // for assert
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

  // for function call/return
  irep_idt function_identifier;

  // for function call
  std::vector<exprt> function_arguments;

  /*! \brief outputs the trace step in ASCII to a given stream
  */
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
};

/*! \brief TO_BE_DOCUMENTED
 * \ingroup gr_goto_symex
*/
class goto_tracet
{
public:
  typedef std::list<goto_trace_stept> stepst;
  stepst steps;

  irep_idt mode;

  void clear()
  {
    mode.clear();
    steps.clear();
  }

  /*! \brief outputs the trace in ASCII to a given stream
  */
  void output(
    const class namespacet &ns,
    std::ostream &out) const;

  void swap(goto_tracet &other)
  {
    other.steps.swap(steps);
    other.mode.swap(mode);
  }

  void add_step(const goto_trace_stept &step)
  {
    steps.push_back(step);
  }

  // retrieves the final step in the trace for manipulation
  // (used to fill a trace from code, hence non-const)
  inline goto_trace_stept &get_last_step()
  {
    return steps.back();
  }

  // delete all steps after (not including) s
  void trim_after(stepst::iterator s)
  {
    PRECONDITION(s != steps.end());
    steps.erase(++s, steps.end());
  }
};

struct trace_optionst
{
  bool json_full_lhs;
  bool hex_representation;
  bool base_prefix;
  bool show_function_calls;
  bool show_code;
  bool stack_trace;

  static const trace_optionst default_options;

  explicit trace_optionst(const optionst &options)
  {
    json_full_lhs = options.get_bool_option("trace-json-extended");
    hex_representation = options.get_bool_option("trace-hex");
    base_prefix = hex_representation;
    show_function_calls = options.get_bool_option("trace-show-function-calls");
    show_code = options.get_bool_option("trace-show-code");
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
    stack_trace = false;
  };
};

void show_goto_trace(
  std::ostream &out,
  const namespacet &,
  const goto_tracet &);

void show_goto_trace(
  std::ostream &out,
  const namespacet &,
  const goto_tracet &,
  const trace_optionst &);

void trace_value(
  std::ostream &out,
  const namespacet &,
  const optionalt<symbol_exprt> &lhs_object,
  const exprt &full_lhs,
  const exprt &value,
  const trace_optionst &);

#define OPT_GOTO_TRACE                                                         \
  "(trace-json-extended)"                                                      \
  "(trace-show-function-calls)"                                                \
  "(trace-show-code)"                                                          \
  "(trace-hex)"                                                                \
  "(stack-trace)"

#define HELP_GOTO_TRACE                                                        \
  " --trace-json-extended        add rawLhs property to trace\n"               \
  " --trace-show-function-calls  show function calls in plain trace\n"         \
  " --trace-show-code            show original code in plain trace\n"          \
  " --trace-hex                  represent plain trace values in hex\n"        \
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
  if(cmdline.isset("stack-trace"))                                             \
    options.set_option("stack-trace", true);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_TRACE_H
