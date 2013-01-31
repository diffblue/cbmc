/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

#include <std_code.h>
#include <std_expr.h>
#include <context.h>

#include <analyses/uninitialized_domain.h>

/*******************************************************************\

   Class: uninitializedt

 Purpose: 

\*******************************************************************/

class uninitializedt
{
public:
  uninitializedt(contextt &_context):
    context(_context),
    ns(_context),
    uninitialized_analysis(ns)
  {
  }

  void add_assertions(goto_programt &goto_program);

protected:
  contextt &context;
  namespacet ns;
  uninitialized_analysist uninitialized_analysis;

  // The variables that need tracking,
  // i.e., are uninitialized and may be read?
  std::set<irep_idt> tracking;
  
  void get_tracking(goto_programt::const_targett i_it);
};

/*******************************************************************\

Function: uninitializedt::get_tracking

  Inputs:

 Outputs:

 Purpose: which variables need tracking,
          i.e., are uninitialized and may be read?

\*******************************************************************/

void uninitializedt::get_tracking(goto_programt::const_targett i_it)
{
  std::list<exprt> objects=objects_read(*i_it);

  forall_expr_list(o_it, objects)
  {
    if(o_it->id()==ID_symbol)
    {
      const irep_idt &identifier=to_symbol_expr(*o_it).get_identifier();
      const std::set<irep_idt> &uninitialized=
        uninitialized_analysis[i_it].uninitialized;
      if(uninitialized.find(identifier)!=uninitialized.end())
        tracking.insert(identifier);
    }
    else if(o_it->id()==ID_dereference)
    {
    }
  }
}

/*******************************************************************\

Function: uninitializedt::add_assertions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uninitializedt::add_assertions(goto_programt &goto_program)
{
  uninitialized_analysis(goto_program);
  
  // find out which variables need tracking

  tracking.clear();
  forall_goto_program_instructions(i_it, goto_program)
    get_tracking(i_it);
    
  // add tracking symbols to symbol table
  for(std::set<irep_idt>::const_iterator
      it=tracking.begin();
      it!=tracking.end();
      it++)
  {
    const symbolt &symbol=ns.lookup(*it);

    symbolt new_symbol;
    new_symbol.name=id2string(symbol.name)+"#initialized";
    new_symbol.type=bool_typet();
    new_symbol.base_name=id2string(symbol.base_name)+"#initialized";
    new_symbol.location=symbol.location;
    new_symbol.mode=symbol.mode;
    new_symbol.module=symbol.module;
    new_symbol.is_thread_local=true;
    new_symbol.is_static_lifetime=false;
    new_symbol.is_file_local=true;
    new_symbol.is_lvalue=true;
    
    context.move(new_symbol);
  }

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

    if(instruction.is_decl())
    {
      // if we track it, add declaration and assignment
      // for tracking variable!

      const irep_idt &identifier=
        to_code_decl(instruction.code).get_identifier();

      if(tracking.find(identifier)!=tracking.end())
      {
        goto_programt::targett i1=goto_program.insert_after(i_it);
        goto_programt::targett i2=goto_program.insert_after(i1);
        i_it++, i_it++;
        
        const irep_idt new_identifier=
          id2string(identifier)+"#initialized";

        symbol_exprt symbol_expr;
        symbol_expr.set_identifier(new_identifier);
        symbol_expr.type()=bool_typet();
        i1->type=DECL;
        i1->location=instruction.location;
        i1->code=code_declt(symbol_expr);

        i2->type=ASSIGN;
        i2->location=instruction.location;
        i2->code=code_assignt(symbol_expr, false_exprt());        
      }
    }
    else
    {
      std::list<exprt> read=objects_read(instruction);
      std::list<exprt> written=objects_written(instruction);

      // if(instruction.is_function_call())
      //const code_function_callt &code_function_call=
      //  to_code_function_call(instruction.code);

      // check tracking variables
      forall_expr_list(it, read)
      {
        if(it->id()==ID_symbol)
        {
          const irep_idt &identifier=to_symbol_expr(*it).get_identifier();
          const std::set<irep_idt> &uninitialized=
            uninitialized_analysis[i_it].uninitialized;

          if(uninitialized.find(identifier)!=uninitialized.end())
          {
            assert(tracking.find(identifier)!=tracking.end());
            const irep_idt new_identifier=id2string(identifier)+"#initialized";
          
            // insert assertion
            goto_programt::instructiont assertion;
            assertion.type=ASSERT;
            assertion.guard=symbol_exprt(new_identifier, bool_typet());
            assertion.location=instruction.location;
            assertion.location.set_comment("use of uninitialized local variable");
            assertion.location.set_property("uninitialized local");
            
            goto_program.insert_before_swap(i_it, assertion);
            i_it++;
          }
        }
      }

      // set tracking variables
      forall_expr_list(it, written)
      {
        if(it->id()==ID_symbol)
        {
          const irep_idt &identifier=to_symbol_expr(*it).get_identifier();

          if(tracking.find(identifier)!=tracking.end())
          {
            const irep_idt new_identifier=id2string(identifier)+"#initialized";
          
            goto_programt::instructiont assignment;
            assignment.type=ASSIGN;
            assignment.code=code_assignt(
              symbol_exprt(new_identifier, bool_typet()), true_exprt());
            assignment.location=instruction.location;
            
            goto_program.insert_before_swap(i_it, assignment);
            i_it++;
          }
        }
      }
    }
  }  
}

/*******************************************************************\

Function: add_uninitialized_locals_assertions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_uninitialized_locals_assertions(
  contextt &context,
  goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    uninitializedt uninitialized(context);

    uninitialized.add_assertions(f_it->second.body);
  }
}

/*******************************************************************\

Function: show_uninitialized

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_uninitialized(
  const class contextt &context,
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  const namespacet ns(context);

  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->second.body_available)
    {
      out << "////" << std::endl;
      out << "//// Function: " << f_it->first << std::endl;
      out << "////" << std::endl;
      out << std::endl;
      uninitialized_analysist uninitialized_analysis(ns);
      uninitialized_analysis(f_it->second.body);
      uninitialized_analysis.output(f_it->second.body, out);
    }
  }

}
