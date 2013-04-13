/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/i2string.h>

#include <langapi/language_util.h>

#include "goto_program.h"

/*******************************************************************\

Function: goto_programt::output_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& goto_programt::output_instruction(
  const class namespacet &ns,
  const irep_idt &identifier,
  std::ostream& out,
  instructionst::const_iterator it) const
{
  out << "        // " << it->location_number << " ";

  if(!it->location.is_nil())
    out << it->location.as_string();
  else
    out << "no location";

  out << "\n";

  if(!it->labels.empty())
  {
    out << "        // Labels:";
    for(instructiont::labelst::const_iterator
        l_it=it->labels.begin();
        l_it!=it->labels.end();
        l_it++)
    {
      out << " " << *l_it;
    }
    
    out << std::endl;
  }

  if(it->is_target())
    out << std::setw(6) << it->target_number << ": ";
  else
    out << "        ";

  switch(it->type)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET" << std::endl;
    break;
  
  case GOTO:
    if(!it->guard.is_true())
    {
      out << "IF "
          << from_expr(ns, identifier, it->guard)
          << " THEN ";
    }

    out << "GOTO ";
    
    for(instructiont::targetst::const_iterator
        gt_it=it->targets.begin();
        gt_it!=it->targets.end();
        gt_it++)
    {
      if(gt_it!=it->targets.begin()) out << ", ";
      out << (*gt_it)->target_number;
    }
      
    out << std::endl;
    break;
    
  case RETURN:
  case OTHER:
  case DECL:
  case DEAD:
  case FUNCTION_CALL:
  case ASSIGN:
    out << from_expr(ns, identifier, it->code) << std::endl;
    break;
    
  case ASSUME:
  case ASSERT:
    if(it->is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";
      
    {
      out << from_expr(ns, identifier, it->guard);
    
      const irep_idt &comment=it->location.get(ID_comment);
      if(comment!="") out << " // " << comment;
    }
      
    out << std::endl;
    break;

  case SKIP:
    out << "SKIP" << std::endl;
    break;
    
  case END_FUNCTION:
    out << "END_FUNCTION" << std::endl;
    break;
    
  case LOCATION:
    out << "LOCATION" << std::endl;
    break;
    
  case THROW:
    out << "THROW";

    {
      const irept::subt &exception_list=
        it->code.find(ID_exception_list).get_sub();
    
      for(irept::subt::const_iterator
          it=exception_list.begin();
          it!=exception_list.end();
          it++)
        out << " " << it->id();
    }
    
    if(it->code.operands().size()==1)
      out << ": " << from_expr(ns, identifier, it->code.op0());
    
    out << std::endl;
    break;
    
  case CATCH:
    if(!it->targets.empty())
    {
      out << "CATCH-PUSH ";
    
      unsigned i=0;
      const irept::subt &exception_list=
        it->code.find(ID_exception_list).get_sub();
      assert(it->targets.size()==exception_list.size());
      for(instructiont::targetst::const_iterator
          gt_it=it->targets.begin();
          gt_it!=it->targets.end();
          gt_it++,
          i++)
      {
        if(gt_it!=it->targets.begin()) out << ", ";
        out << exception_list[i].id() << "->"
            << (*gt_it)->target_number;
      }
    }
    else
      out << "CATCH-POP";
      
    out << std::endl;
    break;
    
  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN" << std::endl;
    break;
    
  case ATOMIC_END:
    out << "ATOMIC_END" << std::endl;
    break;
    
  case START_THREAD:
    out << "START THREAD ";

    if(it->targets.size()==1)
      out << it->targets.front()->target_number;
    
    out << std::endl;
    break;
    
  case END_THREAD:
    out << "END THREAD" << std::endl;
    break;
    
  default:
    throw "unknown statement";
  }

  return out;  
}

/*******************************************************************\

Function: goto_programt::get_decl_identifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_programt::get_decl_identifiers(
  decl_identifierst &decl_identifiers) const
{
  forall_goto_program_instructions(it, (*this))
  {
    if(it->is_decl())
    {
      assert(it->code.get_statement()==ID_decl);
      assert(it->code.operands().size()==1);
      const symbol_exprt &symbol_expr=to_symbol_expr(it->code.op0());
      decl_identifiers.insert(symbol_expr.get_identifier());
    }
  }
} 

/*******************************************************************\

Function: parse_lhs_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parse_lhs_read(const exprt &src, std::list<exprt> &dest)
{
  if(src.id()==ID_dereference)
  {
    assert(src.operands().size()==1);
    dest.push_back(src.op0());
  }
  else if(src.id()==ID_index)
  {
    assert(src.operands().size()==2);
    dest.push_back(src.op1());
    parse_lhs_read(src.op0(), dest);
  }
  else if(src.id()==ID_member)
  {
    assert(src.operands().size()==1);
    parse_lhs_read(src.op0(), dest);
  }
  else if(src.id()==ID_if)
  {
    assert(src.operands().size()==3);
    dest.push_back(src.op0());
    parse_lhs_read(src.op1(), dest);
    parse_lhs_read(src.op2(), dest);
  }
}

/*******************************************************************\

Function: expressions_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> expressions_read(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> dest;

  switch(instruction.type)
  {
  case ASSUME:
  case ASSERT:
  case GOTO:
    dest.push_back(instruction.guard);
    break;
  
  case RETURN:
    if(to_code_return(instruction.code).return_value().is_not_nil())
      dest.push_back(to_code_return(instruction.code).return_value());
    break;
  
  case FUNCTION_CALL:
    {
      const code_function_callt &function_call=
        to_code_function_call(instruction.code);
      forall_expr(it, function_call.arguments())
        dest.push_back(*it);
      if(function_call.lhs().is_not_nil())
        parse_lhs_read(function_call.lhs(), dest);
    }
    break;
  
  case ASSIGN:
    {
      const code_assignt &assignment=to_code_assign(instruction.code);
      dest.push_back(assignment.rhs());
      parse_lhs_read(assignment.lhs(), dest);
    }
    break;
  
  default:;
  }
  
  return dest;
}

/*******************************************************************\

Function: expressions_written

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> expressions_written(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> dest;

  switch(instruction.type)
  {
  case FUNCTION_CALL:
    {
      const code_function_callt &function_call=
        to_code_function_call(instruction.code);
      if(function_call.lhs().is_not_nil())
        dest.push_back(function_call.lhs());
    }
    break;
  
  case ASSIGN:
    dest.push_back(to_code_assign(instruction.code).lhs());
    break;
  
  default:;
  }
  
  return dest;
}

/*******************************************************************\

Function: get_objects_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void objects_read(
  const exprt &src,
  std::list<exprt> &dest) 
{
  if(src.id()==ID_symbol)
    dest.push_back(src);
  else if(src.id()==ID_address_of)
  {
    // don't traverse!
  }
  else if(src.id()==ID_dereference)
  {
    // this reads what is pointed to plus the pointer
    assert(src.operands().size()==1);
    dest.push_back(src);
    objects_read(src.op0(), dest);
  }
  else
  {
    forall_operands(it, src)
      objects_read(*it, dest);
  }
}

/*******************************************************************\

Function: objects_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> objects_read(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> expressions=expressions_read(instruction);

  std::list<exprt> dest;
  
  forall_expr_list(it, expressions)
    objects_read(*it, dest);
  
  return dest;
}

/*******************************************************************\

Function: objects_written

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void objects_written(
  const exprt &src,
  std::list<exprt> &dest)
{
  if(src.id()==ID_if)
  {
    assert(src.operands().size()==3);
    objects_written(src.op1(), dest);
    objects_written(src.op2(), dest);
  }
  else
    dest.push_back(src);
}

/*******************************************************************\

Function: objects_written

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> objects_written(
  const goto_programt::instructiont &instruction)
{
  std::list<exprt> expressions=expressions_written(instruction);

  std::list<exprt> dest;
  
  forall_expr_list(it, expressions)
    objects_written(*it, dest);
  
  return dest;
}

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string as_string(
  const class namespacet &ns,
  const goto_programt::instructiont &i)
{
  std::string result;

  switch(i.type)
  {
  case NO_INSTRUCTION_TYPE:
    return "(NO INSTRUCTION TYPE)";
    
  case GOTO:
    if(!i.guard.is_true())
    {
      result+="IF "
            +from_expr(ns, i.function, i.guard)
            +" THEN ";
    }

    result+="GOTO ";
    
    for(goto_programt::instructiont::targetst::const_iterator
        gt_it=i.targets.begin();
        gt_it!=i.targets.end();
        gt_it++)
    {
      if(gt_it!=i.targets.begin()) result+=", ";
      result+=i2string((*gt_it)->target_number);
    }
    return result;
    
  case RETURN:
  case OTHER:
  case DECL:
  case DEAD:
  case FUNCTION_CALL:
  case ASSIGN:
    return from_expr(ns, i.function, i.code);
    
  case ASSUME:
  case ASSERT:
    if(i.is_assume())
      result+="ASSUME ";
    else
      result+="ASSERT ";
      
    result+=from_expr(ns, i.function, i.guard);

    {
      const irep_idt &comment=i.location.get(ID_comment);
      if(comment!="") result+="/* "+id2string(comment)+" */";
    }
    return result;

  case SKIP:
    return "SKIP";
    
  case END_FUNCTION:
    return "END_FUNCTION";
    
  case LOCATION:
    return "LOCATION";
    
  case THROW:
    return "THROW";
    
  case CATCH:
    return "CATCH";
    
  case ATOMIC_BEGIN:
    return "ATOMIC_BEGIN";
    
  case ATOMIC_END:
    return "ATOMIC_END";
    
  case START_THREAD:
    result+="START THREAD ";

    if(i.targets.size()==1)
      result+=i2string(i.targets.front()->target_number);
    return result;
    
  case END_THREAD:
    return "END THREAD";
    
  default:
    throw "unknown statement";
  }

  return "";
}

