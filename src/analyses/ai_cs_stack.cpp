/*******************************************************************\

Module: Stack for context-sensitive analysis

Author: Daniel Poetzl, Peter Schrammel

\*******************************************************************/

#include "ai_cs_stack.h"

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: print stack element

\*******************************************************************/

std::ostream &operator<<(
  std::ostream &out,
  const ai_cs_stackt::stack_elementt &stack_element)
{
  const irep_idt func = std::get<0>(stack_element);
  const ai_cs_stackt::locationt l = std::get<1>(stack_element);
  const ai_cs_stackt::stack_element_typet set = std::get<2>(stack_element);

  out << "(" << id2string(func) << ", ";
  out << "(" << l->location_number << ", " << l->source_location << "), ";
  if (set == ai_cs_stackt::SE_FUNCTION_CALL) {
    out << "function_call";
  } else {
    assert(set == ai_cs_stackt::SE_THREAD_CREATE);
    out << "thread_create";
  }
  out << ")";
  return out;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: print stack

\*******************************************************************/

std::ostream &operator<<(std::ostream &out, const ai_cs_stackt &stack)
{
  out << "[";
  bool first = true;
  for (const ai_cs_stackt::stack_elementt &stack_element : stack.frames)
  {
    if (!first) {
      out << ", ";
    }
    first = false;
    out << stack_element;
  }
  out << "]";
  return out;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_stackt::parse_stack(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  const std::string &s)
{
  frames.clear();

  if (s.empty())
    return;

  typedef std::vector<std::string> string_vectort;

  // get stack frames
  string_vectort result;
  misc::split_string(s, ';', result, true);
  chk(!result.empty(), "no stack frames");

  get_targett get_target(goto_functions, ns);

  // get stack frame components
  for(string_vectort::const_iterator it=result.begin();
      it!=result.end(); it++)
  {
    string_vectort triple;
    misc::split_string(*it, ',', triple, true);
    chk(triple.size()==3, "wrong stack frame length");

    irep_idt id(triple[0]);

    get_targett::rest res=get_target.from_spec(triple[1]);
    chk(res.first, "");
    locationt loc=res.second;

    stack_element_typet set;
    if (triple[2]=="thread_create")
      set=SE_THREAD_CREATE;
    else if(triple[2]=="function_call")
      set=SE_FUNCTION_CALL;
    else
      chk(false, "wrong call or thread indicator");

    frames.push_back(make_tuple(id, loc, set));
  }
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_stackt::is_valid_location(
 const goto_functionst &goto_functions,
 locationt loc) const
{
  irep_idt id=loc->function;
  goto_functionst::function_mapt::const_iterator it
    =goto_functions.function_map.find(id);

  if(it==goto_functions.function_map.end())
  {
    std::cout << "YYY a" << std::endl;
    return false;
  }

  const goto_functiont &goto_function=it->second;
  if(!goto_function.body_available())
  {
    std::cout << "YYY b" << std::endl;
    return false;
  }

  const goto_programt &goto_program=goto_function.body;
  forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it==loc)
      return true;
  }

  std::cout << loc->function << std::endl;
  std::cout << "YYY c" << std::endl;
  return false;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_stackt::is_valid_stack(
  const goto_functionst &goto_functions) const
{
  for(framest::const_iterator it=frames.begin(); it!=frames.end(); it++)
  {
    irep_idt id=std::get<0>(*it); // callee
    locationt loc=std::get<1>(*it); // location in callee
    stack_element_typet set=std::get<2>(*it);

    if(loc->function!=id)
    {
      std::cout << "XXX a" << std::endl;
      return false;
    }
    if(!is_valid_location(goto_functions, loc))
    {
      std::cout << "XXX b" << std::endl;
      return false;
    }
    if(!loc->is_function_call())
    {
      std::cout << "XXX c" << std::endl;
      return false;
    }

    irep_idt called_fun=misc::get_function_name(loc);

    if(set==SE_THREAD_CREATE)
    {
      if(id2string(called_fun)!=config.ansi_c.create_thread)
      {
        std::cout << "XXX d" << std::endl;
        return false;
      }
    }
    else
    {
      if(set!=SE_FUNCTION_CALL)
      {
        std::cout << "XXX e" << std::endl;
        return false;
      }
      if(id2string(called_fun)==config.ansi_c.create_thread)
      {
        std::cout << "XXX f" << std::endl;
        return false;
      }
    }
  }
  return true;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ai_cs_stackt::remove_top_calls()
{
  while(!frames.empty())
  {
    stack_elementt se=frames.back();
    stack_element_typet set=std::get<2>(se);
    if (set==SE_FUNCTION_CALL)
      frames.pop_back();
    else
    {
      assert(set==SE_THREAD_CREATE);
      break;
    }
  }

  assert(!has_top_calls());
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ai_cs_stackt::has_top_calls() const
{
  if(!frames.empty())
  {
    stack_elementt se=frames.back();
    stack_element_typet set=std::get<2>(se);
    return set==SE_FUNCTION_CALL;
  }
  return false;
}
