/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <prefix.h>

#include <ansi-c/expr2c.h>

#include "dump_c.h"

/*******************************************************************\

Function: convert_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string convert_id(const irep_idt &id)
{
  std::string result=id2string(id);
  
  if(has_prefix(result, "c::"))
    result=std::string(result, 3, std::string::npos);
  
  return result;
}

/*******************************************************************\

Function: gen_indent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_indent(unsigned indent, std::ostream &out)
{
  for(unsigned i=0; i<indent; i++) out << ' ' << ' ';
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  unsigned indent,
  const goto_programt &goto_program,
  const goto_programt::const_targett t,
  const namespacet &ns,
  std::ostream &out)
{
  switch(t->type)
  {
  case GOTO:
    break;
  
  case ASSUME:
    break;
  
  case ASSERT:
    break;
  
  case OTHER:
    break;
    
  case DECL:
    break;
  
  case SKIP:
  case LOCATION:
  case END_FUNCTION:
    // ignore
    break;

  case DEAD:
    out << "/* ignoring DEAD */" << std::endl << std::endl;
    break;
  
  case START_THREAD:
    out << "/* ignoring START_THREAD */" << std::endl << std::endl;
    break;
  
  case END_THREAD:
    out << "/* ignoring END_THREAD */" << std::endl << std::endl;
    break;
  
  case ATOMIC_BEGIN:
    out << "/* ignoring ATOMIC_BEGIN */" << std::endl << std::endl;
    break;

  case ATOMIC_END:
    out << "/* ignoring ATOMIC_END */" << std::endl << std::endl;
    break;
  
  case RETURN:
    gen_indent(indent, out);
    out << "return";
    out << ";" << std::endl;
    break;
  
  case ASSIGN:
    break;
  
  case FUNCTION_CALL:
    break;
  
  default:
    throw "unexpected goto instruction";
  }
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  const goto_functionst::function_mapt::const_iterator f_it,
  const namespacet &ns,
  std::ostream &out)
{
  out << "/* " << f_it->first << " */" << std::endl;

  const symbolt &symbol=ns.lookup(f_it->first);
  
  out << "/* " << symbol.location << " */" << std::endl;
  out << std::endl;

  const code_typet &type=to_code_type(ns.follow(symbol.type));
  
  out << type2c(type.return_type(), ns);
  out << " ";
  out << convert_id(symbol.name);
  
  const code_typet::argumentst &arguments=
    type.arguments();

  if(arguments.empty())
  {
    out << "(void)" << std::endl;
  }
  else
  {
    out << "(" << std::endl;
    for(code_typet::argumentst::const_iterator
        a_it=arguments.begin();
        a_it!=arguments.end();
        a_it++)
    {
      if(a_it!=arguments.begin()) out << ", " << std::endl;
      out << "  ";
      out << type2c(a_it->type(), ns);
      out << " " << convert_id(a_it->get_identifier());
    }
    out << ")" << std::endl;
  }
  
  out << "{" << std::endl;
  
  const goto_programt &body=f_it->second.body;

  forall_goto_program_instructions(it, body)
    dump_c(1, body, it, ns, out);

  out << "}  /* end of " << symbol.name << " */" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: dump_c

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void dump_c(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out)
{
  forall_goto_functions(it, src)
    if(it->second.body_available &&
       it->first!="main")
      dump_c(it, ns, out);
}
