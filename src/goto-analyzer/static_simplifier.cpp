/*******************************************************************\

Module:

Author: Lucas Cordeiro, lucas.cordeiro@cs.ox.ac.uk

\*******************************************************************/

#include "static_simplifier.h"

#include <iostream>
#include <fstream>
#include <string>

#include <goto-programs/write_goto_binary.h>
#include <goto-instrument/dump_c.h>


/*******************************************************************\

Function: collect_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void collect_operands(const exprt &src, std::vector<exprt> &dest)
{
  for(const exprt &op : src.operands())
  {
    if(op.id()==src.id())
      collect_operands(op, dest);
    else
      dest.push_back(op);
  }
}

bool static_simplifiert::has_global_variable(const exprt &guard)
{
  bool result=false;
  std::vector<exprt> operands;
  collect_operands(guard, operands);

  if (operands.size()==1)
  {
    const exprt op=operands[0];
    irep_idt identifier;

    if (op.op0().id()==ID_symbol)
   	  identifier=op.op0().get(ID_identifier);
    else if (op.op1().id()==ID_symbol)
   	  identifier=op.op1().get(ID_identifier);
    else
      return false;

    const symbolt *symbol;
    if(ns.lookup(identifier, symbol))
      throw "failed to find symbol "+id2string(identifier);

    if(symbol->is_static_lifetime)
     result=true;
  }
  else if(operands.size()>=2)
  {
    for(unsigned i=0; i<operands.size(); i++)
      result = has_global_variable(operands[i]);
  }

  return result;
}

/*******************************************************************\

Function: static_simplifiert::simplify_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_simplifiert::simplify_guards()
{
  unsigned simplified[]={0,0,0}, unknown[]={0,0,0};
  bool is_pthread=false;

  if (constant_propagation)
    propagate_constants();

  if (intervals)
    interval_analysis(goto_functions, ns);

  status() << "simplifying guards" << eom;

  Forall_goto_functions(f_it, goto_functions)
  {
	if(f_it->first=="pthread_create")
	  is_pthread=true;

    if(f_it->first=="__actual_thread_spawn")
      continue;

    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert() || i_it->is_assume()
        || i_it->is_goto())
      {
        tvt r=eval(i_it);

        if (is_pthread && has_global_variable(i_it->guard)) continue;

        if(r.is_true())
    	  i_it->guard=true_exprt();
        else if(r.is_false())
    	  i_it->guard=false_exprt();

        //summarize the simplification results
        if (r.is_true() || r.is_false())
        {
      	  if (i_it->is_assert())
      	    simplified[0]+=1;
      	  else if (i_it->is_assume())
      		simplified[1]+=1;
      	  else
      		simplified[2]+=1;
        }
        else
        {
       	  if (i_it->is_assert())
       		unknown[0]+=1;
       	  else if (i_it->is_assume())
       		unknown[1]+=1;
       	  else
       		unknown[2]+=1;
        }
      }
    }
  }
  status() << "SIMPLIFIED: " << " assert: " << simplified[0]
		   << ", assume: " << simplified[1]
		   << ", goto: " << simplified[2] << "\n"
		   << "UNKNOWN: " << "    assert: " << unknown[0]
		   << ", assume: " << unknown[1]
		   << ", goto: " << unknown[2] << eom;

  //make sure the references are correct
  goto_functions.update();
}

/*******************************************************************\

Function: static_simplifiert::write_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool static_simplifiert::write_goto_program(const std::string &filename)
{
  status() << "Writing GOTO program to `" << filename << "'" << eom;

  //write the simplified goto program
  if(write_goto_binary(
	 filename, symbol_table, goto_functions, get_message_handler()))
    return 1;
  else
    return 0;
}

/*******************************************************************\

Function: static_simplifiert::write_c_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_simplifiert::write_c_program(const std::string &filename, const bool h)
{
	status() << "Writing simplified C program to `" << filename << "'" << eom;

  //redirect std::cout to filename
  std::ofstream out(filename);
  std::cout.rdbuf(out.rdbuf());

  //write the simplified C program
  dump_c(goto_functions, h, ns, std::cout);
}
