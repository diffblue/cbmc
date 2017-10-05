/*******************************************************************\

Module: goto_statistics.cpp

Author: Marek Trtik

\*******************************************************************/

#include "goto_statistics.h"
#include <sstream>

void goto_statisticst::extend(
  const goto_functionst &functions,
  const symbol_tablet &table)
{
  for(auto const &elem : functions.function_map)
  {
    if(!elem.second.body_available())
      continue;
    for(const auto &instr : elem.second.body.instructions)
    {
      switch(instr.type)
      {
        case FUNCTION_CALL:
          ++num_function_calls;
          break;
        case ASSERT:
          ++num_assertions;
          break;
        case ASSUME:
          ++num_assumptions;
          break;
        case GOTO:
          if (instr.guard.is_true())
            ++num_unconditional_gotos;
          else
            ++num_conditional_gotos;
          if(instr.is_backwards_goto())
            ++num_loops;
          break;
        default:
          break;
      }
      ++num_instructions;
    }
    ++num_functions;
  }
  for(const auto &name_symbol : table.symbols)
  {
    if(name_symbol.second.is_lvalue && name_symbol.second.is_state_var)
    {
      if(name_symbol.second.is_auxiliary)
        ++num_auxiliary_variables;
      else
        ++num_user_variables;
    }
  }
}

jsont to_json(const goto_statisticst &stats)
{
  json_objectt json_stats;
  json_stats["num_functions"]=
    json_numbert(std::to_string(stats.get_num_functions()));
  json_stats["num_instructions"]=
    json_numbert(std::to_string(stats.get_num_instructions()));
  json_stats["num_user_variables"]=
    json_numbert(std::to_string(stats.get_num_user_variables()));
  json_stats["num_auxiliary_variables"]=
    json_numbert(std::to_string(stats.get_num_auxiliary_variables()));
  json_stats["num_function_calls"]=
    json_numbert(std::to_string(stats.get_num_function_calls()));
  json_stats["num_unconditional_gotos"]=
    json_numbert(std::to_string(stats.get_num_unconditional_gotos()));
  json_stats["num_conditional_gotos"]=
    json_numbert(std::to_string(stats.get_num_conditional_gotos()));
  json_stats["num_loops"]=
    json_numbert(std::to_string(stats.get_num_loops()));

  return json_stats;
}
