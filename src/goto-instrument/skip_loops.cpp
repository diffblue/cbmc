/*******************************************************************\

Module: Skip over selected loops by adding gotos

Author: Michael Tautschnig

Date: January 2016

\*******************************************************************/

#include <util/message.h>
#include <util/string2int.h>

#include <goto-programs/goto_functions.h>

#include "skip_loops.h"

typedef std::set<unsigned> loop_idst;
typedef std::map<irep_idt, loop_idst> loop_mapt;

/*******************************************************************\

Function: skip_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool skip_loops(
  goto_programt &goto_program,
  const loop_idst &loop_ids,
  messaget &message)
{
  loop_idst::const_iterator l_it=loop_ids.begin();
  Forall_goto_program_instructions(it, goto_program)
  {
    if(l_it==loop_ids.end()) break;
    if(!it->is_backwards_goto()) continue;

    const unsigned loop_id=it->loop_number;
    if(*l_it<loop_id) break; // error handled below
    if(*l_it>loop_id) continue;

    goto_programt::targett loop_head=it->get_target();
    goto_programt::targett next=it;
    ++next;
    assert(next!=goto_program.instructions.end());

    goto_programt::targett g=goto_program.insert_before(loop_head);
    g->make_goto(next, true_exprt());
    g->source_location=loop_head->source_location;
    g->function=loop_head->function;

    ++l_it;
  }
  if(l_it!=loop_ids.end())
  {
    message.error() << "Loop " << *l_it << " not found"
                    << messaget::eom;
    return true;
  }

  return false;
}

/*******************************************************************\

Function: skip_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool parse_loop_ids(
  const std::string &loop_ids,
  loop_mapt &loop_map)
{
  std::string::size_type length=loop_ids.length();

  for(std::string::size_type idx=0; idx<length; idx++)
  {
    std::string::size_type next=loop_ids.find(",", idx);
    std::string val=loop_ids.substr(idx, next-idx);
    std::string::size_type delim=val.rfind(".");

    if(delim==std::string::npos) return true;

    std::string fn=val.substr(0, delim);
    unsigned nr=safe_string2unsigned(val.substr(delim+1));

    loop_map[fn].insert(nr);

    if(next==std::string::npos) break;
    idx=next;
  }

  return false;
}

/*******************************************************************\

Function: skip_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool skip_loops(
  goto_functionst &goto_functions,
  const std::string &loop_ids,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  loop_mapt loop_map;
  if(parse_loop_ids(loop_ids, loop_map))
  {
    message.error() << "Failed to parse loop ids" << messaget::eom;
    return true;
  }

  loop_mapt::const_iterator it=loop_map.begin();
  Forall_goto_functions(f_it, goto_functions)
  {
    if(it==loop_map.end() || it->first<f_it->first)
      break; // possible error handled below
    else if(it->first==f_it->first)
    {
      if(skip_loops(f_it->second.body, it->second, message))
        return true;
      ++it;
    }
  }
  if(it!=loop_map.end())
  {
    message.error() << "No function " << it->first << " in goto program"
                    << messaget::eom;
    return true;
  }

  // update counters etc.
  goto_functions.update();

  return false;
}
