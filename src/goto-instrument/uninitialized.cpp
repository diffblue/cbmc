/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

/// \file
/// Detection for Uninitialized Local Variables

#include "uninitialized.h"

#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <analyses/uninitialized_domain.h>

class uninitializedt
{
public:
  explicit uninitializedt(symbol_tablet &_symbol_table):
    symbol_table(_symbol_table),
    ns(_symbol_table)
  {
  }

  void add_assertions(
    const irep_idt &function_identifer,
    goto_programt &goto_program);

protected:
  symbol_tablet &symbol_table;
  namespacet ns;
  uninitialized_analysist uninitialized_analysis;

  // The variables that need tracking,
  // i.e., are uninitialized and may be read?
  std::set<irep_idt> tracking;

  void get_tracking(goto_programt::const_targett i_it);
};

/// which variables need tracking, i.e., are uninitialized and may be read?
void uninitializedt::get_tracking(goto_programt::const_targett i_it)
{
  std::list<exprt> objects=objects_read(*i_it);

  for(const auto &object : objects)
  {
    if(object.id() == ID_symbol)
    {
      const irep_idt &identifier = to_symbol_expr(object).get_identifier();
      const std::set<irep_idt> &uninitialized=
        uninitialized_analysis[i_it].uninitialized;
      if(uninitialized.find(identifier)!=uninitialized.end())
        tracking.insert(identifier);
    }
    else if(object.id() == ID_dereference)
    {
    }
  }
}

void uninitializedt::add_assertions(
  const irep_idt &function_identifier,
  goto_programt &goto_program)
{
  uninitialized_analysis(function_identifier, goto_program, ns);

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

    symbol_table.insert(std::move(new_symbol));
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
        i1->source_location=instruction.source_location;
        i1->code=code_declt(symbol_expr);

        i2->type=ASSIGN;
        i2->source_location=instruction.source_location;
        i2->code=code_assignt(symbol_expr, false_exprt());
      }
    }
    else
    {
      std::list<exprt> read=objects_read(instruction);
      std::list<exprt> written=objects_written(instruction);

      // if(instruction.is_function_call())
      // const code_function_callt &code_function_call=
      //  to_code_function_call(instruction.code);

      const std::set<irep_idt> &uninitialized=
        uninitialized_analysis[i_it].uninitialized;

      // check tracking variables
      for(const auto &object : read)
      {
        if(object.id() == ID_symbol)
        {
          const irep_idt &identifier = to_symbol_expr(object).get_identifier();

          if(uninitialized.find(identifier)!=uninitialized.end())
          {
            assert(tracking.find(identifier)!=tracking.end());
            const irep_idt new_identifier=id2string(identifier)+"#initialized";

            // insert assertion
            goto_programt::instructiont assertion;
            assertion.type=ASSERT;
            assertion.guard=symbol_exprt(new_identifier, bool_typet());
            assertion.source_location=instruction.source_location;
            assertion.source_location.set_comment(
              "use of uninitialized local variable");
            assertion.source_location.set_property_class("uninitialized local");

            goto_program.insert_before_swap(i_it, assertion);
            i_it++;
          }
        }
      }

      // set tracking variables
      for(const auto &object : written)
      {
        if(object.id() == ID_symbol)
        {
          const irep_idt &identifier = to_symbol_expr(object).get_identifier();

          if(tracking.find(identifier)!=tracking.end())
          {
            const irep_idt new_identifier=id2string(identifier)+"#initialized";

            goto_programt::instructiont assignment;
            assignment.type=ASSIGN;
            assignment.code=code_assignt(
              symbol_exprt(new_identifier, bool_typet()), true_exprt());
            assignment.source_location=instruction.source_location;

            goto_program.insert_before_swap(i_it, assignment);
            i_it++;
          }
        }
      }
    }
  }
}

void add_uninitialized_locals_assertions(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    uninitializedt uninitialized(goto_model.symbol_table);

    uninitialized.add_assertions(f_it->first, f_it->second.body);
  }
}

void show_uninitialized(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  const namespacet ns(goto_model.symbol_table);

  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(f_it->second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << f_it->first << '\n';
      out << "////\n\n";
      uninitialized_analysist uninitialized_analysis;
      uninitialized_analysis(f_it->first, f_it->second.body, ns);
      uninitialized_analysis.output(ns, f_it->second.body, out);
    }
  }
}
