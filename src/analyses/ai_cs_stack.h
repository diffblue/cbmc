/*******************************************************************\

Module: Stack for context-sensitive analysis

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ANALYSES_AI_CS_STACK_H
#define CPROVER_ANALYSES_AI_CS_STACK_H

#include <map>
#include <tuple>
#include <stack>
#include <queue>
#include <utility>
#include <iosfwd>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>
#include <util/misc_utils.h>
#include <util/numbering.h>
#include <analyses/get_target.h>

class ai_cs_stackt
{
public:
  typedef goto_programt::const_targett locationt;

  typedef enum {
    SE_FUNCTION_CALL,
    SE_THREAD_CREATE
  } stack_element_typet;

  // caller, location of call, stack element type
  typedef std::tuple<irep_idt, locationt, stack_element_typet> stack_elementt;
  typedef std::list<stack_elementt> framest;
  
  framest frames;

  typedef goto_functionst::goto_functiont goto_functiont;

  void parse_stack(
    const goto_functionst &goto_functions,
    const namespacet &ns,
    const std::string &s);

  bool is_valid_stack(const goto_functionst &goto_functions) const;

  // remove topmost function calls which are not thread creates
  void remove_top_calls();

  bool has_top_calls() const;

  bool operator<(const ai_cs_stackt &other) const
  {
    return frames<other.frames;
  }

  bool operator==(const ai_cs_stackt &other) const
  {
    return frames==other.frames;
  }

protected:
  bool is_valid_location(
    const goto_functionst &goto_functions,
    locationt loc) const;
};

std::ostream &operator<<(
  std::ostream &out,
  const ai_cs_stackt::stack_elementt &stack_element);

std::ostream &operator<<(std::ostream &out, const ai_cs_stackt &stack);

typedef numbering_one<ai_cs_stackt> stack_numberingt;
typedef trie_numbering<ai_cs_stackt::stack_elementt> trie_stack_numberingt;

#endif
