/*******************************************************************\

Module: Havoc Loops

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Havoc Loops

#include "havoc_loops.h"

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>

#include <goto-programs/remove_skip.h>

#include "function_assigns.h"
#include "havoc_utils.h"
#include "loop_utils.h"

class havoc_loopst
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;

  havoc_loopst(
    function_assignst &_function_assigns,
    goto_functiont &_goto_function)
    : goto_function(_goto_function),
      local_may_alias(_goto_function),
      function_assigns(_function_assigns),
      natural_loops(_goto_function.body)
  {
    havoc_loops();
  }

protected:
  goto_functiont &goto_function;
  local_may_aliast local_may_alias;
  function_assignst &function_assigns;
  natural_loops_mutablet natural_loops;

  typedef std::set<exprt> assignst;
  typedef const natural_loops_mutablet::natural_loopt loopt;

  void havoc_loops();

  void havoc_loop(
    const goto_programt::targett loop_head,
    const loopt &);

  void get_assigns(const loopt &, assignst &);
};

void havoc_loopst::havoc_loop(
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

  // first find out what can get changed in the loop
  assignst assigns;
  get_assigns(loop, assigns);

  // build the havocking code
  goto_programt havoc_code;
  havoc_utilst havoc_gen(assigns);
  havoc_gen.append_full_havoc_code(loop_head->source_location(), havoc_code);

  // Now havoc at the loop head. Use insert_swap to
  // preserve jumps to loop head.
  goto_function.body.insert_before_swap(loop_head, havoc_code);

  // compute the loop exit
  goto_programt::targett loop_exit=
    get_loop_exit(loop);

  // divert all gotos to the loop head to the loop exit
  for(loopt::const_iterator
      l_it=loop.begin(); l_it!=loop.end(); l_it++)
  {
    goto_programt::instructiont &instruction=**l_it;
    if(instruction.is_goto())
    {
      for(goto_programt::targetst::iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        if(*t_it==loop_head)
          *t_it=loop_exit; // divert
      }
    }
  }

  // remove skips
  remove_skip(goto_function.body);
}

void havoc_loopst::get_assigns(const loopt &loop, assignst &assigns)
{
  for(const auto &instruction_it : loop)
    function_assigns.get_assigns(local_may_alias, instruction_it, assigns);
}

void havoc_loopst::havoc_loops()
{
  // iterate over the (natural) loops in the function

  for(const auto &loop : natural_loops.loop_map)
    havoc_loop(loop.first, loop.second);
}

void havoc_loops(goto_modelt &goto_model)
{
  function_assignst function_assigns(goto_model.goto_functions);

  for(auto &gf_entry : goto_model.goto_functions.function_map)
    havoc_loopst(function_assigns, gf_entry.second);
}
