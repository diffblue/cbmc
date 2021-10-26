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

#include <util/namespace.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_functions.h>

/// Returns the compile type of an exception
irep_idt uncaught_exceptions_domaint::get_exception_type(const typet &type)
{
  PRECONDITION(type.id()==ID_pointer);

  if(type.subtype().id() == ID_struct_tag)
    return to_struct_tag_type(type.subtype()).get_identifier();
  else
    return ID_empty;
}

/// Returns the symbol corresponding to an exception
exprt uncaught_exceptions_domaint::get_exception_symbol(const exprt &expr)
{
  if(expr.id() != ID_symbol && expr.operands().size() >= 1)
    return get_exception_symbol(to_multi_ary_expr(expr).op0());

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

  switch(instruction.type())
  {
  case THROW:
  {
    const exprt &exc_symbol = get_exception_symbol(instruction.get_code());
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
    if(!instruction.get_code().has_operands())
    {
      if(!instruction.targets.empty()) // push
      {
        std::set<irep_idt> caught;
        stack_caught.push_back(caught);
        std::set<irep_idt> &last_caught=stack_caught.back();
        const irept::subt &exception_list =
          instruction.get_code().find(ID_exception_list).get_sub();

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
    const exprt &function_expr = instruction.call_function();
    DATA_INVARIANT(
      function_expr.id()==ID_symbol,
      "identifier expected to be a symbol");
    const irep_idt &function_name=
      to_symbol_expr(function_expr).get_identifier();
    // use the current information about the callee
    join(uea.exceptions_map[function_name]);
    break;
  }
  case DECL:   // Safe to ignore in this context
  case DEAD:   // Safe to ignore in this context
  case ASSIGN: // Safe to ignore in this context
    break;
  case SET_RETURN_VALUE:
#if 0
    DATA_INVARIANT(false, "Returns must be removed before analysis");
#endif
    break;
  case GOTO:         // Ignoring the guard is a valid over-approximation
  case ATOMIC_BEGIN: // Ignoring is a valid over-approximation
  case ATOMIC_END:   // Ignoring is a valid over-approximation
  case START_THREAD: // Require a concurrent analysis at higher level
  case END_THREAD:   // Require a concurrent analysis at higher level
  case END_FUNCTION: // No action required
  case ASSERT:       // No action required
  case ASSUME:       // Ignoring is a valid over-approximation
  case LOCATION:     // No action required
  case SKIP:         // No action required
    break;
  case OTHER:
#if 0
    DATA_INVARIANT(false, "Unclear what is a safe over-approximation of OTHER");
#endif
    break;
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    DATA_INVARIANT(false, "Only complete instructions can be analyzed");
    break;
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
    for(const auto &gf_entry : goto_functions.function_map)
    {
      domain.make_top();
      const goto_programt &goto_program = gf_entry.second.body;

      if(goto_program.empty())
        continue;

      forall_goto_program_instructions(instr_it, goto_program)
      {
        domain.transform(instr_it, *this, ns);
      }
      // did our estimation for the current function improve?
      const std::set<irep_idt> &elements=domain.get_elements();
      if(exceptions_map[gf_entry.first].size() < elements.size())
      {
        change=true;
        exceptions_map[gf_entry.first] = elements;
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
  for(const auto &gf_entry : goto_functions.function_map)
  {
    const auto fn = gf_entry.first;
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
