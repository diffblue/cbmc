/*******************************************************************\

Module: Over-approximating uncaught exceptions analysis

Author: Cristina David

\*******************************************************************/

/// \file
/// Over-approximating uncaught exceptions analysis

#ifdef DEBUG
#include <iostream>
#endif
#include "uncaught_exceptions_analysis.h"

/// Returns the compile type of an exception
irep_idt uncaught_exceptions_domaint::get_exception_type(const typet &type)
{
  irep_idt candidate;
  bool new_subtype=true;
  const symbol_tablet &symbol_table=ns.get_symbol_table();

  // as we don't know the order types have been recorded,
  // we need to iterate over the symbol table until there are no more
  // new subtypes found
  while(new_subtype)
  {
    new_subtype=false;
    // iterate over the symbol_table in order to find subtypes of type
    forall_symbols(it, symbol_table.symbols)
    {
      // we only look at type entries
      if(it->second.is_type)
      {
        // every type is a potential candidate
        candidate=it->second.name;
        // current candidate is already in subtypes
        if(find(subtypes.begin(),
                subtypes.end(),
                candidate)!=subtypes.end())
          continue;
        // get its base class
        const class_typet::basest &bases=
          to_class_type((it->second).type).bases();
        if(bases.size()>0)
        {
          const class_typet::baset &base = bases[0];
          const irept &base_type=base.find(ID_type);
          assert(base_type.id()==ID_symbol);

          // is it derived from type?
          // i.e. does it have type or one of its subtypes as a base?
          if(base_type.get(ID_identifier)==type ||
             find(subtypes.begin(), subtypes.end(),
                  base_type.get(ID_identifier))!=subtypes.end())
          {
            subtypes.insert(candidate);
            new_subtype=true;
          }
        }
      }
    }
  }
}

/// Returns the symbol corresponding to an exception
exprt uncaught_exceptions_domaint::get_exception_symbol(const exprt &expr)
{
  if(type.id()==ID_pointer)
  {
    return get_static_type(type.subtype());
  }
  else if(type.id()==ID_symbol)
  {
     return to_symbol_type(type).get_identifier();
  }
  return ID_empty;
}

/// The join operator for the uncaught exceptions domain
void uncaught_exceptions_domaint::join(
  const irep_idt &element)
{
  thrown.insert(element);
}

void uncaught_exceptions_domaint::join(
  const std::set<irep_idt> &elements)
{
  thrown.insert(elements.begin(), elements.end());
}


/// The transformer for the uncaught exceptions domain
void uncaught_exceptions_domaint::transform(
  const goto_programt::const_targett from,
  uncaught_exceptions_analysist &uea,
  const namespacet &ns)
{
  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case THROW:
  {
    const exprt &exc_symbol=instruction.code;

    // retrieve the static type of the thrown exception
    const irep_idt &type_id=get_static_type(exc_symbol.type());
    join(type_id);
    // we must consider all the subtypes given that
    // the runtime type is a subtype of the static type
    std::set<irep_idt> subtypes;
    get_subtypes(type_id, subtypes, ns);
    join(subtypes);
    break;
  }
  case CATCH:
  {
    if(!instruction.code.has_operands())
    {
      if(!instruction.targets.empty()) // push
      {
        std::set<irep_idt> caught;
        stack_caught.push_back(caught);
        std::set<irep_idt> &last_caught=stack_caught.back();
        const irept::subt &exception_list=
          instruction.code.find(ID_exception_list).get_sub();

        for(const auto &exc : exception_list)
        {
          last_caught.insert(exc.id());
          std::set<irep_idt> subtypes;
          get_subtypes(exc.id(), subtypes, ns);
          last_caught.insert(subtypes.begin(), subtypes.end());
        }
      }
      else // pop
      {
        if(!stack_caught.empty())
        {
          const std::set<irep_idt> &caught=stack_caught.back();
          join(caught);
          // remove the caught exceptions
          for(const auto &exc_id : caught)
          {
            const std::set<irep_idt>::iterator it=
              std::find(thrown.begin(), thrown.end(), exc_id);
            if(it!=thrown.end())
              thrown.erase(it);
          }
          stack_caught.pop_back();
        }
      }
    }
    break;
  }
  case FUNCTION_CALL:
  {
    const exprt &function_expr=
      to_code_function_call(instruction.code).function();
    assert(function_expr.id()==ID_symbol);
    const irep_idt &function_name=
      to_symbol_expr(function_expr).get_identifier();
    // use the current information about the callee
    join(uea.exceptions_map[function_name]);
    break;
  }
  default:
  {}
  }
}

/// Returns the value of the private member thrown
const std::set<irep_idt> &uncaught_exceptions_domaint::get_elements() const
{
  return thrown;
}

/// Constructs the class hierarchy
void uncaught_exceptions_domaint::operator()(
  const namespacet &ns)
{
  elements=thrown;
}

/// Runs the uncaught exceptions analysis, which  populates the exceptions map
void uncaught_exceptions_analysist::collect_uncaught_exceptions(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  bool change=true;

  while(change)
  {
    change=false;
    // add all the functions to the worklist
    forall_goto_functions(current_function, goto_functions)
    {
      domain.make_top();
      const goto_programt &goto_program=current_function->second.body;

      if(goto_program.empty())
        continue;

      forall_goto_program_instructions(instr_it, goto_program)
      {
        domain.transform(instr_it, *this, ns);
      }
      // did our estimation for the current function improve?
      std::set<irep_idt> elements;
      domain.get_elements(elements);
      change=change||
        exceptions_map[current_function->first].size()!=elements.size();
      exceptions_map[current_function->first]=elements;
    }
  }
}

/// Prints the exceptions map that maps each method to the  set of exceptions
/// that may escape it
void uncaught_exceptions_analysist::output(
  const goto_functionst &goto_functions)
{
#ifdef DEBUG
  forall_goto_functions(it, goto_functions)
  {
    if(exceptions_map[it->first].size()>0)
    {
      std::cout << "Uncaught exceptions in function " <<
        it->first << ": " << std::endl;
      assert(exceptions_map.find(it->first)!=exceptions_map.end());
      for(auto exc_id : exceptions_map[it->first])
        std::cout << id2string(exc_id) << " ";
      std::cout << std::endl;
    }
  }
#endif
}

/// Applies the uncaught exceptions analysis and  outputs the result
void uncaught_exceptions_analysist::operator()(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  exceptions_mapt &exceptions)
{
  collect_uncaught_exceptions(goto_functions, ns);
  exceptions=exceptions_map;
  output(goto_functions);
}

/// Applies the uncaught exceptions analysis and  outputs the result
void uncaught_exceptions(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  std::map<irep_idt, std::set<irep_idt>> &exceptions_map)
{
  uncaught_exceptions_analysist exceptions;
  exceptions(goto_functions, ns, exceptions_map);
}
