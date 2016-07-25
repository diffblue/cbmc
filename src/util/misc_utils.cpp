#include <cctype>

#include <util/ui_message.h>

#include "misc_utils.h"

namespace misc
{

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt get_identifier(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    return to_symbol_expr(expr).get_identifier();
  }
  return irep_idt(); // return empty string
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt get_function_name(goto_programt::const_targett l)
{
  assert(l->is_function_call());
  const code_function_callt &code=to_code_function_call(l->code);
  const exprt &function=code.function();
  return get_identifier(function);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_goto_instruction(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  std::ostream &out,
  goto_programt::const_targett l)
{
  irep_idt id=l->function;
  goto_functionst::function_mapt::const_iterator f_it
    =goto_functions.function_map.find(id);
  assert(f_it!=goto_functions.function_map.end());
  const goto_functiont &goto_function=f_it->second;
  assert(goto_function.body_available());
  const goto_programt &goto_program=goto_function.body;
  goto_program.output_instruction(ns, id, std::cout, l);
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string strip_string(const std::string &s)
{
  unsigned n=s.length();

  // find first non-space char
  unsigned i;
  for(i=0; i<n; i++)
  {
    if(!std::isspace(s[i]))
      break;
  }
  if(i==n)
    return "";

  // find last non-space char
  long j; //otherwise the loop might not terminate
  for (j=n-1; j>=0; j--)
  {
    if(!std::isspace(s[j]))
      break;
  }

  return s.substr(i, (j-i+1));
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void split_string(
  const std::string &s,
  char delim,
  std::vector<std::string> &result,
  bool strip)
{
  assert(result.empty());

  unsigned start=0;
  unsigned i;
  for (i=0; i<s.length(); i++)
  {
    if (s[i]==delim)
    {
      if(i==start)
      {
        start++;
        continue;
      }
      std::string new_s=s.substr(start, i-start);
      if (strip)
        new_s=strip_string(new_s);
      result.push_back(new_s);
      start=i+1;
    }
  }
  if(i!=start)
  {
    std::string new_s=s.substr(start, i-start);
    if (strip)
      new_s=strip_string(new_s);
    result.push_back(new_s);
  }

  assert(!result.empty());
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_location_number_map(
  const goto_functionst &goto_functions,
  std::map<unsigned, goto_programt::const_targett> &map)
{
  assert(map.empty());

  forall_goto_functions(it, goto_functions)
  {
    const goto_functionst::goto_functiont &goto_function=it->second;
    if (!goto_function.body_available())
      continue;

    const goto_programt &goto_program=it->second.body;
    forall_goto_program_instructions(i_it, goto_program)
    {
      map.insert(std::make_pair(i_it->location_number, i_it));
    }
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_locations(
  const goto_functionst &goto_functions,
  std::set<goto_programt::const_targett> &set)
{
  assert(set.empty());

  forall_goto_functions(it, goto_functions)
  {
    const goto_functionst::goto_functiont &goto_function=it->second;
    if (!goto_function.body_available())
      continue;

    const goto_programt &goto_program=it->second.body;
    forall_goto_program_instructions(i_it, goto_program)
    {
      set.insert(i_it);
    }
  }
}

} // namespace end
