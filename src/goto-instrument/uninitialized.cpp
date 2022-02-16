/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

/// \file
/// Detection for Uninitialized Local Variables

#include "uninitialized.h"

#include <util/std_code.h>
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

      const irep_idt &identifier = instruction.decl_symbol().get_identifier();

      if(tracking.find(identifier)!=tracking.end())
      {
        const irep_idt new_identifier=
          id2string(identifier)+"#initialized";

        symbol_exprt symbol_expr(new_identifier, bool_typet());
        goto_programt::instructiont i1 =
          goto_programt::make_decl(symbol_expr, instruction.source_location());

        goto_programt::instructiont i2 = goto_programt::make_assignment(
          symbol_expr, false_exprt(), instruction.source_location());

        goto_programt::targett i1_it =
          goto_program.insert_after(i_it, std::move(i1));
        goto_program.insert_after(i1_it, std::move(i2));
        i_it++, i_it++;
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
            goto_programt::instructiont assertion =
              goto_programt::make_assertion(
                symbol_exprt(new_identifier, bool_typet()),
                instruction.source_location());
            assertion.source_location_nonconst().set_comment(
              "use of uninitialized local variable " + id2string(identifier));
            assertion.source_location_nonconst().set_property_class(
              "uninitialized local");

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

            goto_programt::instructiont assignment =
              goto_programt::make_assignment(
                symbol_exprt(new_identifier, bool_typet()),
                true_exprt(),
                instruction.source_location());

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
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    uninitializedt uninitialized(goto_model.symbol_table);

    uninitialized.add_assertions(gf_entry.first, gf_entry.second.body);
  }
}

void show_uninitialized(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  const namespacet ns(goto_model.symbol_table);

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
    {
      out << "////\n";
      out << "//// Function: " << gf_entry.first << '\n';
      out << "////\n\n";
      uninitialized_analysist uninitialized_analysis;
      uninitialized_analysis(gf_entry.first, gf_entry.second.body, ns);
      uninitialized_analysis.output(
        ns, gf_entry.first, gf_entry.second.body, out);
    }
  }
}
