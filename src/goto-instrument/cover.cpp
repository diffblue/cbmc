/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#include <util/i2string.h>

#include "cover.h"

class basic_blockst
{
public:
  explicit basic_blockst(const goto_programt &_goto_program)
  {
    bool next_is_target=true;
    unsigned block_count=0;

    forall_goto_program_instructions(it, _goto_program)
    {
      if(next_is_target || it->is_target())
        block_count++;
        
      block_map[it]=block_count;
      
      next_is_target=
        it->is_goto() || it->is_return() ||
        it->is_function_call() || it->is_assume();
    }
  }
  
  typedef std::map<goto_programt::const_targett, unsigned> block_mapt;
  block_mapt block_map;
  
  inline unsigned operator[](goto_programt::const_targett t)
  {
    return block_map[t];
  }
  
  void output(std::ostream &out)
  {
    for(block_mapt::const_iterator
        b_it=block_map.begin();
        b_it!=block_map.end();
        b_it++)
      out << b_it->first->source_location
          << " -> " << b_it->second
          << '\n';
  }
};

const char *as_string(coverage_criteriont c)
{
  switch(c)
  {
  case coverage_criteriont::LOCATION: return "location";
  case coverage_criteriont::BRANCH: return "branch";
  case coverage_criteriont::DECISION: return "decision";
  case coverage_criteriont::CONDITION: return "condition";
  case coverage_criteriont::PATH: return "path";
  case coverage_criteriont::MCDC: return "MC/DC";
  case coverage_criteriont::ASSERTION: return "assertion";
  default: return "";
  }
}

/*******************************************************************\

Function: instrument_cover_goals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont criterion)
{
  basic_blockst basic_blocks(goto_program);
  std::set<unsigned> blocks_done;
  
  Forall_goto_program_instructions(i_it, goto_program)
  {
    switch(criterion)
    {
    case coverage_criteriont::ASSERTION:
      break;
      
    case coverage_criteriont::LOCATION:
      {
        unsigned block_nr=basic_blocks[i_it];
        if(blocks_done.insert(block_nr).second)
        {
          std::string b=i2string(block_nr);
          std::string id=id2string(i_it->function)+"#"+b;
          if(i_it->source_location.get_file()!="")
          {
            std::string comment=
              "block "+i_it->source_location.as_string();

            source_locationt source_location=i_it->source_location;
            goto_program.insert_before_swap(i_it);
            i_it->make_assertion(false_exprt());
            i_it->source_location=source_location;
            i_it->source_location.set_comment(comment);
          }
        }
      }
      break;
    
    case coverage_criteriont::BRANCH:
      if(i_it->is_goto() && !i_it->guard.is_true())
      {
        #if 0
        std::string b=i2string(basic_blocks[i_it]);
        goal_map[id(i_it, "TRUE")]=
          goalt("function "+id2string(f_it->first)+" block "+b+" branch true",
                i_it->source_location);
        goal_map[id(i_it, "FALSE")]=
          goalt("function "+id2string(f_it->first)+" block "+b+" branch false",
                i_it->source_location);
        #endif
      }
      break;
      
    case coverage_criteriont::CONDITION:
      if(i_it->is_goto())
      {
        #if 0
        std::set<exprt> conditions;

        collect_conditions(i_it->guard, conditions);
        unsigned i=0;

        for(std::set<exprt>::const_iterator it=conditions.begin();
            it!=conditions.end();
            it++, i++)
        {
          goal_map[id(i_it, "C"+i2string(i))]=
            goalt("condition "+from_expr(bmc.ns, "", *it),
                  i_it->source_location);
        }
        #endif
      }
      break;
    
    default:;
    }
  }

}

/*******************************************************************\

Function: instrument_cover_goals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont criterion)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->first==ID__start ||
       f_it->first=="__CPROVER_initialize")
      continue;
      
    instrument_cover_goals(symbol_table, f_it->second.body, criterion);
  }
}

/*******************************************************************\

Function: bmc_covert::collect_conditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void bmc_covert::collect_conditions(const exprt &src, std::set<exprt> &dest)
{
  if(src.id()==ID_and || src.id()==ID_or ||
     src.id()==ID_not || src.id()==ID_implies)
  {
    forall_operands(it, src)
      collect_conditions(*it, dest);
  }
  else if(src.is_true())
  {
  }
  else
  {
    dest.insert(src); 
  }
}
#endif

/*******************************************************************\

Function: bmc_covert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

