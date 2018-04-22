/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS_H

#include <unordered_set>

#include <util/message.h>
#include <util/json.h>

#include "goto_functions.h"

class goto_inlinet:public messaget
{
public:
  goto_inlinet(
    goto_functionst &goto_functions,
    const namespacet &ns,
    message_handlert &message_handler,
    bool adjust_function,
    bool caching=true):
    messaget(message_handler),
    goto_functions(goto_functions),
    ns(ns),
    adjust_function(adjust_function),
    caching(caching)
  {
  }

  typedef goto_functionst::goto_functiont goto_functiont;

  // call that should be inlined
  // false:    inline non-transitively
  // true:     inline transitively
  typedef std::pair<goto_programt::targett, bool> callt;

  // list of calls that should be inlined
  typedef std::list<callt> call_listt;

  // list of calls per function that should be inlined
  typedef std::map<irep_idt, call_listt> inline_mapt;

  // handle given goto function
  // force_full:
  // - true:  put skip on recursion and issue warning
  // - false: leave call on recursion
  void goto_inline(
    const irep_idt identifier,
    goto_functiont &goto_function,
    const inline_mapt &inline_map,
    const bool force_full=false);

  // handle all functions
  void goto_inline(
    const inline_mapt &inline_map,
    const bool force_full=false);

  void output_inline_map(
    std::ostream &out,
    const inline_mapt &inline_map);

  void output_cache(std::ostream &out) const;

  // call after goto_functions.update()!
  jsont output_inline_log_json()
  {
    inline_log.cleanup(cache);
    return inline_log.output_inline_log_json();
  }

  // get call info of normal or bp call
  static void get_call(
    goto_programt::const_targett target,
    exprt &lhs,
    exprt &function,
    exprt::operandst &arguments);

  class goto_inline_logt
  {
  public:
    class goto_inline_log_infot
    {
    public:
      // original segment location numbers
      unsigned begin_location_number;
      unsigned end_location_number;
      unsigned call_location_number; // original call location number
      irep_idt function; // function from which segment was inlined
      goto_programt::const_targett end; // segment end
    };

    // remove segment that refer to the given goto program
    void cleanup(const goto_programt &goto_program);

    void cleanup(const goto_functionst::function_mapt &function_map);

    void add_segment(
      const goto_programt &goto_program,
      const unsigned begin_location_number,
      const unsigned end_location_number,
      const unsigned call_location_number,
      const irep_idt function);

    void copy_from(const goto_programt &from, const goto_programt &to);

    // call after goto_functions.update()!
    jsont output_inline_log_json() const;

    // map from segment start to inline info
    typedef std::map<
      goto_programt::const_targett,
      goto_inline_log_infot> log_mapt;

    log_mapt log_map;
  };

protected:
  goto_functionst &goto_functions;
  const namespacet &ns;

  const bool adjust_function;
  const bool caching;

  goto_inline_logt inline_log;

  void goto_inline_nontransitive(
    const irep_idt identifier,
    goto_functiont &goto_function,
    const inline_mapt &inline_map,
    const bool force_full);

  const goto_functiont &goto_inline_transitive(
    const irep_idt identifier,
    const goto_functiont &goto_function,
    const bool force_full);

  bool check_inline_map(const inline_mapt &inline_map) const;
  bool check_inline_map(
    const irep_idt identifier,
    const inline_mapt &inline_map) const;

  bool is_ignored(const irep_idt id) const;

  void clear()
  {
    cache.clear();
    finished_set.clear();
    recursion_set.clear();
    no_body_set.clear();
  }

  void expand_function_call(
    goto_programt &dest,
    const inline_mapt &inline_map,
    const bool transitive,
    const bool force_full,
    goto_programt::targett target);

  void insert_function_body(
    const goto_functiont &f,
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs,
    const symbol_exprt &function,
    const exprt::operandst &arguments);

  void replace_return(
    goto_programt &body,
    const exprt &lhs);

  void parameter_assignments(
    const goto_programt::targett target,
    const irep_idt &function_name,
    const code_typet &code_type,
    const exprt::operandst &arguments,
    goto_programt &dest);

  void parameter_destruction(
    const goto_programt::targett target,
    const irep_idt &function_name,
    const code_typet &code_type,
    goto_programt &dest);

  // goto functions that were already inlined transitively
  typedef goto_functionst::function_mapt cachet;
  cachet cache;

  typedef std::unordered_set<irep_idt> finished_sett;
  finished_sett finished_set;

  typedef std::unordered_set<irep_idt> recursion_sett;
  recursion_sett recursion_set;

  typedef std::unordered_set<irep_idt> no_body_sett;
  no_body_sett no_body_set;
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_INLINE_CLASS_H
