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
  PRECONDITION(type.id()==ID_pointer);

  if(type.subtype().id() == ID_symbol_type)
    return to_symbol_type(type.subtype()).get_identifier();
  else
    return ID_empty;
}

/// Returns the symbol corresponding to an exception
exprt uncaught_exceptions_domaint::get_exception_symbol(const exprt &expr)
{
  if(expr.id()!=ID_symbol && expr.has_operands())
    return get_exception_symbol(expr.op0());

  return expr;
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

void uncaught_exceptions_domaint::join(
  const std::vector<irep_idt> &elements)
{
  thrown.insert(elements.begin(), elements.end());
}


/// The transformer for the uncaught exceptions domain
void uncaught_exceptions_domaint::transform(
  const goto_programt::const_targett from,
  uncaught_exceptions_analysist &uea,
  const namespacet &)
{
  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case THROW:
  {
    const exprt &exc_symbol=get_exception_symbol(instruction.code);
    // retrieve the static type of the thrown exception
    const irep_idt &type_id=get_exception_type(exc_symbol.type());
    join(type_id);
    // we must consider all the subtypes given that
    // the runtime type is a subtype of the static type
    std::vector<irep_idt> subtypes =
      class_hierarchy.get_children_trans(type_id);
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
          std::vector<irep_idt> subtypes=
            class_hierarchy.get_children_trans(exc.id());
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
            thrown.erase(exc_id);
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
    DATA_INVARIANT(
      function_expr.id()==ID_symbol,
      "identifier expected to be a symbol");
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
  class_hierarchy(ns.get_symbol_table());
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
      const std::set<irep_idt> &elements=domain.get_elements();
      if(exceptions_map[current_function->first].size()<elements.size())
      {
        change=true;
        exceptions_map[current_function->first]=elements;
      }
    }
  }
}

/// Prints the exceptions map that maps each method to the  set of exceptions
/// that may escape it
void uncaught_exceptions_analysist::output(
  const goto_functionst &goto_functions) const
{
  (void)goto_functions; // unused parameter
#ifdef DEBUG
  forall_goto_functions(it, goto_functions)
  {
    const auto fn=it->first;
    const exceptions_mapt::const_iterator found=exceptions_map.find(fn);
    // Functions like __CPROVER_assert and __CPROVER_assume are replaced by
    // explicit GOTO instructions and will not show up in exceptions_map.
    if(found==exceptions_map.end())
      continue;

    const auto &fs=found->second;
    if(!fs.empty())
    {
      std::cout << "Uncaught exceptions in function " <<
        fn << ": " << std::endl;
      for(const auto exc_id : fs)
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
  domain(ns);
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
