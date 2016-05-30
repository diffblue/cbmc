/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#include <algorithm>

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
      
      if(!it->source_location.is_nil() &&
         source_location_map.find(block_count)==source_location_map.end())
        source_location_map[block_count]=it->source_location;
      
      next_is_target=
        it->is_goto() || it->is_function_call();
    }
  }

  // map program locations to block numbers  
  typedef std::map<goto_programt::const_targett, unsigned> block_mapt;
  block_mapt block_map;
  
  // map block numbers to source code locations
  typedef std::map<unsigned, source_locationt> source_location_mapt;
  source_location_mapt source_location_map;
  
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
  case coverage_criteriont::COVER: return "cover instructions";
  default: return "";
  }
}

/*******************************************************************\

Function: collect_conditions_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_conditions_rec(const exprt &src, std::set<exprt> &dest)
{
  if(src.id()==ID_address_of)
  {
    return;
  }

  for(const auto & op : src.operands())
    collect_conditions_rec(op, dest);

  if(src.type().id()==ID_bool)
  {
    if(src.id()==ID_and || src.id()==ID_or ||
       src.id()==ID_not || src.id()==ID_implies)
    {
      // ignore me
    }
    else if(src.is_constant())
    {
      // ignore me
    }
    else
    {
      dest.insert(src); 
    }
  }
}

/*******************************************************************\

Function: collect_conditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> collect_conditions(const exprt &src)
{
  std::set<exprt> result;
  collect_conditions_rec(src, result);
  return result;
}

/*******************************************************************\

Function: collect_conditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> collect_conditions(const goto_programt::const_targett t)
{
  switch(t->type)
  {
  case GOTO:
  case ASSERT:
    return collect_conditions(t->guard);
  
  case ASSIGN:
  case FUNCTION_CALL:
    return collect_conditions(t->code);
    
  default:;
  }
  
  return std::set<exprt>();
}

/*******************************************************************\

Function: collect_decisions_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_decisions_rec(const exprt &src, std::set<exprt> &dest)
{
  if(src.id()==ID_address_of)
  {
    return;
  }

  if(src.type().id()==ID_bool)
  {
    if(src.is_constant())
    {
      // ignore me
    }
    else if(src.id()==ID_not)
    {
      collect_decisions_rec(src.op0(), dest);
    }
    else
    {
      dest.insert(src); 
    }
  }
  else
  {
    for(const auto & op : src.operands())
      collect_decisions_rec(op, dest);
  }
}

/*******************************************************************\

Function: collect_decisions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> collect_decisions(const exprt &src)
{
  std::set<exprt> result;
  collect_decisions_rec(src, result);
  return result;
}

/*******************************************************************\

Function: collect_decisions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> collect_decisions(const goto_programt::const_targett t)
{
  switch(t->type)
  {
  case GOTO:
  case ASSERT:
    return collect_decisions(t->guard);
  
  case ASSIGN:
  case FUNCTION_CALL:
    return collect_decisions(t->code);
    
  default:;
  }
  
  return std::set<exprt>();
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
  const namespacet ns(symbol_table);
  basic_blockst basic_blocks(goto_program);
  std::set<unsigned> blocks_done;
  
  Forall_goto_program_instructions(i_it, goto_program)
  {
    switch(criterion)
    {
    case coverage_criteriont::ASSERTION:
      // turn into 'assert(false)' to avoid simplification
      if(i_it->is_assert())
        i_it->guard=false_exprt();
      break;
      
    case coverage_criteriont::COVER:
      // turn __CPROVER_cover(x) into 'assert(!x)'
      if(i_it->is_function_call())
      {
        const code_function_callt &code_function_call=
          to_code_function_call(i_it->code);
        if(code_function_call.function().id()==ID_symbol &&
           to_symbol_expr(code_function_call.function()).get_identifier()==
           "__CPROVER_cover" &&
           code_function_call.arguments().size()==1)
        {
          const exprt c=code_function_call.arguments()[0];
          std::string comment="condition `"+from_expr(ns, "", c)+"'";
          i_it->guard=not_exprt(c);
          i_it->type=ASSERT;
          i_it->code.clear();
          i_it->source_location.set_comment(comment);
        }
      }
      else if(i_it->is_assert())
        i_it->make_skip();
      break;
      
    case coverage_criteriont::LOCATION:
      if(i_it->is_assert())
        i_it->make_skip();

      {
        unsigned block_nr=basic_blocks[i_it];
        if(blocks_done.insert(block_nr).second)
        {
          std::string b=i2string(block_nr);
          std::string id=id2string(i_it->function)+"#"+b;
          source_locationt source_location=
            basic_blocks.source_location_map[block_nr];
          
          if(!source_location.get_file().empty() &&
             source_location.get_file()[0]!='<')
          {
            std::string comment="block "+b;
            goto_program.insert_before_swap(i_it);
            i_it->make_assertion(false_exprt());
            i_it->source_location=source_location;
            i_it->source_location.set_comment(comment);
            
            i_it++;
          }
        }
      }
      break;
    
    case coverage_criteriont::BRANCH:
      if(i_it->is_goto() && !i_it->guard.is_true())
      {
        std::string b=i2string(basic_blocks[i_it]);
        std::string true_comment=
          "function "+id2string(i_it->function)+" block "+b+" branch true";
        std::string false_comment=
          "function "+id2string(i_it->function)+" block "+b+" branch false";

        exprt guard=i_it->guard;
        source_locationt source_location=i_it->source_location;

        goto_program.insert_before_swap(i_it);
        i_it->make_assertion(not_exprt(guard));
        i_it->source_location=source_location;
        i_it->source_location.set_comment(true_comment);

        goto_program.insert_before_swap(i_it);
        i_it->make_assertion(guard);
        i_it->source_location=source_location;
        i_it->source_location.set_comment(false_comment);
        
        i_it++;
        i_it++;
      }
      else if(i_it->is_assert())
        i_it->make_skip();

      break;
      
    case coverage_criteriont::CONDITION:
      if(i_it->is_assert())
        i_it->make_skip();

      // Conditions are all atomic predicates in the programs.
      {
        const std::set<exprt> conditions=collect_conditions(i_it);

        const source_locationt source_location=i_it->source_location;

        for(const auto & c : conditions)
        {
          const std::string c_string=from_expr(ns, "", c);
        
          const std::string comment_t="condition `"+c_string+"' true";
          goto_program.insert_before_swap(i_it);
          i_it->make_assertion(c);
          i_it->source_location=source_location;
          i_it->source_location.set_comment(comment_t);

          const std::string comment_f="condition `"+c_string+"' false";
          goto_program.insert_before_swap(i_it);
          i_it->make_assertion(not_exprt(c));
          i_it->source_location=source_location;
          i_it->source_location.set_comment(comment_f);
        }
        
        for(unsigned i=0; i<conditions.size()*2; i++)
          i_it++;
      }
      break;
    
    case coverage_criteriont::DECISION:
      if(i_it->is_assert())
        i_it->make_skip();

      // Decisions are maximal Boolean combinations of conditions.
      {
        const std::set<exprt> decisions=collect_decisions(i_it);

        const source_locationt source_location=i_it->source_location;

        for(const auto & d : decisions)
        {
          const std::string d_string=from_expr(ns, "", d);
        
          const std::string comment_t="decision `"+d_string+"' true";
          goto_program.insert_before_swap(i_it);
          i_it->make_assertion(d);
          i_it->source_location=source_location;
          i_it->source_location.set_comment(comment_t);

          const std::string comment_f="decision `"+d_string+"' false";
          goto_program.insert_before_swap(i_it);
          i_it->make_assertion(not_exprt(d));
          i_it->source_location=source_location;
          i_it->source_location.set_comment(comment_f);
        }
        
        for(unsigned i=0; i<decisions.size()*2; i++)
          i_it++;
      }
      break;
      
    case coverage_criteriont::MCDC:
      if(i_it->is_assert())
        i_it->make_skip();

      // 1. Each entry and exit point is invoked
      // 2. Each decision takes every possible outcome
      // 3. Each condition in a decision takes every possible outcome
      // 4. Each condition in a decision is shown to independently
      //    affect the outcome of the decision.
      {
        const std::set<exprt> conditions=collect_conditions(i_it);
        const std::set<exprt> decisions=collect_decisions(i_it);
        
        std::set<exprt> both;
        std::set_union(conditions.begin(), conditions.end(),
                       decisions.begin(), decisions.end(),
                       inserter(both, both.end()));

        const source_locationt source_location=i_it->source_location;

        for(const auto & p : both)
        {
          bool is_decision=decisions.find(p)!=decisions.end();
          bool is_condition=conditions.find(p)!=conditions.end();
          
          std::string description=
            (is_decision && is_condition)?"decision/condition":
            is_decision?"decision":"condition";
            
          std::string p_string=from_expr(ns, "", p);
        
          std::string comment_t=description+" `"+p_string+"' true";
          goto_program.insert_before_swap(i_it);
          i_it->make_assertion(p);
          i_it->source_location=source_location;
          i_it->source_location.set_comment(comment_t);

          std::string comment_f=description+" `"+p_string+"' false";
          goto_program.insert_before_swap(i_it);
          i_it->make_assertion(not_exprt(p));
          i_it->source_location=source_location;
          i_it->source_location.set_comment(comment_f);
        }
        
        for(unsigned i=0; i<both.size()*2; i++)
          i_it++;
      }
      break;

    case coverage_criteriont::PATH:
      if(i_it->is_assert())
        i_it->make_skip();
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
