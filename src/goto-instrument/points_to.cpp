/*******************************************************************\

Module: Field-sensitive, location-insensitive points-to analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Field-sensitive, location-insensitive points-to analysis

#include "points_to.h"

void points_tot::fixedpoint()
{
  // this loop iterates until fixed-point

  bool added;

  do
  {
    added=false;

    for(const auto &instruction_and_entry : cfg.entries())
    {
      if(transform(cfg[instruction_and_entry.second]))
        added=true;
    }
  }
  while(added);
}

void points_tot::output(std::ostream &out) const
{
  for(value_mapt::const_iterator
      v_it=value_map.begin();
      v_it!=value_map.end();
      v_it++)
  {
    out << v_it->first << ":";

    for(object_id_sett::const_iterator
        o_it=v_it->second.begin();
        o_it!=v_it->second.end();
        o_it++)
    {
      out << " " << *o_it;
    }

    out << '\n';
  }
}

bool points_tot::transform(const cfgt::nodet &e)
{
  bool result=false;
  const goto_programt::instructiont &instruction=*(e.PC);

  switch(instruction.type())
  {
  case SET_RETURN_VALUE:
    // TODO
    break;

  case ASSIGN:
    {
      // const code_assignt &code_assign=to_code_assign(instruction.code);
    }
    break;

  case FUNCTION_CALL:
    // these are like assignments for the arguments
    break;

  case CATCH:
  case THROW:
  case GOTO:
  case DEAD:
  case DECL:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case LOCATION:
  case OTHER:
  case SKIP:
  case ASSERT:
  case ASSUME:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    break;
  }

  return result;
}
