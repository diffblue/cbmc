/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: April 2016

\*******************************************************************/

#include "variable_sensitivity_domain.h"

#include <util/cprover_prefix.h>
#include <util/symbol_table.h>

#include <algorithm>

#ifdef DEBUG
#  include <iostream>
#endif

void variable_sensitivity_domaint::transform(
  const irep_idt &function_from,
  trace_ptrt trace_from,
  const irep_idt &function_to,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};
  locationt to{trace_to->current_location()};

#ifdef DEBUG
  std::cout << "Transform from/to:\n";
  std::cout << from->location_number << " --> " << to->location_number << '\n';
#endif

  const goto_programt::instructiont &instruction = *from;
  switch(instruction.type())
  {
  case DECL:
  {
    abstract_object_pointert top_object =
      abstract_state
        .abstract_object_factory(
          instruction.decl_symbol().type(), ns, true, false)
        ->write_location_context(from);
    abstract_state.assign(instruction.decl_symbol(), top_object, ns);
  }
  // We now store top.
  break;

  case DEAD:
    // Remove symbol from map, the only time this occurs now (keep TOP.)
    // It should be the case that DEAD only provides symbols for deletion.
    abstract_state.erase(instruction.dead_symbol());
    break;

  case ASSIGN:
  {
    // TODO : check return values
    abstract_object_pointert rhs =
      abstract_state.eval(instruction.assign_rhs(), ns)
        ->write_location_context(from);
    abstract_state.assign(instruction.assign_lhs(), rhs, ns);
  }
  break;

  case GOTO:
  {
    if(flow_sensitivity == flow_sensitivityt::sensitive)
    {
      // Get the next line
      locationt next = from;
      next++;
      // Is this a GOTO to the next line (i.e. pointless)
      if(next != from->get_target())
      {
        if(to == from->get_target())
        {
          // The AI is exploring the branch where the jump is taken
          assume(instruction.condition(), ns);
        }
        else
        {
          // Exploring the path where the jump is not taken - therefore assume
          // the condition is false
          assume(not_exprt(instruction.condition()), ns);
        }
      }
      // ignore jumps to the next line, we can assume nothing
    }
  }
  break;

  case ASSUME:
    assume(instruction.condition(), ns);
    break;

  case FUNCTION_CALL:
  {
    transform_function_call(from, to, ai, ns);
    break;
  }

  case END_FUNCTION:
  {
    // erase parameters

    const irep_idt id = function_from;
    const symbolt &symbol = ns.lookup(id);

    const code_typet &type = to_code_type(symbol.type);

    for(const auto &param : type.parameters())
    {
      // Top the arguments to the function
      abstract_state.assign(
        symbol_exprt(param.get_identifier(), param.type()),
        abstract_state.abstract_object_factory(param.type(), ns, true, false),
        ns);
    }

    break;
  }

    /***************************************************************/

  case ASSERT:
    // Conditions on the program, do not alter the data or information
    // flow and thus can be ignored.
    // Checking of assertions can only be reasonably done once the fix-point
    // has been computed, i.e. after all of the calls to transform.
    break;

  case SKIP:
  case LOCATION:
    // Can ignore
    break;

  case SET_RETURN_VALUE:
    throw "the SET_RETURN_VALUE instructions should be removed first";

  case START_THREAD:
  case END_THREAD:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    throw "threading not supported";

  case THROW:
  case CATCH:
    throw "exceptions not handled";

  case OTHER:
    //    throw "other";
    break;

  case NO_INSTRUCTION_TYPE:
    break;
  case INCOMPLETE_GOTO:
    break;
  default:
    throw "unrecognised instruction type";
  }

  DATA_INVARIANT(abstract_state.verify(), "Structural invariant");
}

void variable_sensitivity_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  abstract_state.output(out, ai, ns);
}

exprt variable_sensitivity_domaint::to_predicate() const
{
  return abstract_state.to_predicate();
}

exprt variable_sensitivity_domaint::to_predicate(
  const exprt &expr,
  const namespacet &ns) const
{
  auto result = abstract_state.eval(expr, ns);
  return result->to_predicate(expr);
}

exprt variable_sensitivity_domaint::to_predicate(
  const exprt::operandst &exprs,
  const namespacet &ns) const
{
  if(exprs.empty())
    return false_exprt();
  if(exprs.size() == 1)
    return to_predicate(exprs.front(), ns);

  auto predicates = std::vector<exprt>{};
  std::transform(
    exprs.cbegin(),
    exprs.cend(),
    std::back_inserter(predicates),
    [this, &ns](const exprt &expr) { return to_predicate(expr, ns); });
  return and_exprt(predicates);
}

void variable_sensitivity_domaint::make_bottom()
{
  abstract_state.make_bottom();
  return;
}

void variable_sensitivity_domaint::make_top()
{
  abstract_state.make_top();
}

void variable_sensitivity_domaint::make_entry()
{
  abstract_state.make_top();
}

bool variable_sensitivity_domaint::merge(
  const variable_sensitivity_domaint &b,
  trace_ptrt from,
  trace_ptrt to)
{
#ifdef DEBUG
  std::cout << "Merging from/to:\n " << from->location_number << " --> "
            << to->location_number << '\n';
#endif
  auto widen_mode =
    from->should_widen(*to) ? widen_modet::could_widen : widen_modet::no;
  // Use the abstract_environment merge
  bool any_changes =
    abstract_state.merge(b.abstract_state, to->current_location(), widen_mode);

  DATA_INVARIANT(abstract_state.verify(), "Structural invariant");
  return any_changes;
}

bool variable_sensitivity_domaint::ai_simplify(
  exprt &condition,
  const namespacet &ns) const
{
  abstract_object_pointert res = abstract_state.eval(condition, ns);
  exprt c = res->to_constant();

  if(c.id() == ID_nil)
  {
    bool no_simplification = true;

    // Try to simplify recursively any child operations
    for(exprt &op : condition.operands())
    {
      no_simplification &= ai_simplify(op, ns);
    }

    return no_simplification;
  }
  else
  {
    bool condition_changed = (condition != c);
    condition = c;
    return !condition_changed;
  }
}

bool variable_sensitivity_domaint::is_bottom() const
{
  return abstract_state.is_bottom();
}

bool variable_sensitivity_domaint::is_top() const
{
  return abstract_state.is_top();
}

std::vector<irep_idt> variable_sensitivity_domaint::get_modified_symbols(
  const variable_sensitivity_domaint &other) const
{
  return abstract_environmentt::modified_symbols(
    abstract_state, other.abstract_state);
}

void variable_sensitivity_domaint::transform_function_call(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  PRECONDITION(from->type() == FUNCTION_CALL);

  const exprt &function = from->call_function();

  const locationt next = std::next(from);

  if(function.id() == ID_symbol)
  {
    // called function identifier
    const symbol_exprt &symbol_expr = to_symbol_expr(function);
    const irep_idt function_id = symbol_expr.get_identifier();

    const code_function_callt::argumentst &called_arguments =
      from->call_arguments();

    if(to->location_number == next->location_number)
    {
      if(ignore_function_call_transform(function_id))
      {
        return;
      }

      if(0) // Sound on opaque function calls
      {
        abstract_state.havoc("opaque function call");
      }
      else
      {
        // For any parameter that is a non-const pointer, top the value it is
        // pointing at.
        for(const exprt &called_arg : called_arguments)
        {
          if(
            called_arg.type().id() == ID_pointer &&
            !called_arg.type().subtype().get_bool(ID_C_constant))
          {
            abstract_object_pointert pointer_value =
              abstract_state.eval(called_arg, ns);

            CHECK_RETURN(pointer_value);

            // Write top to the pointer
            pointer_value->write(
              abstract_state,
              ns,
              std::stack<exprt>(),
              nil_exprt(),
              abstract_state.abstract_object_factory(
                called_arg.type().subtype(), ns, true, false),
              false);
          }
        }

        // Top any global values
        for(const auto &symbol : ns.get_symbol_table().symbols)
        {
          if(symbol.second.is_static_lifetime)
          {
            abstract_state.assign(
              symbol_exprt(symbol.first, symbol.second.type),
              abstract_state.abstract_object_factory(
                symbol.second.type, ns, true, false),
              ns);
          }
        }
      }
    }
    else
    {
      // we have an actual call
      const symbolt &symbol = ns.lookup(function_id);
      const code_typet &code_type = to_code_type(symbol.type);
      const code_typet::parameterst &declaration_parameters =
        code_type.parameters();

      code_typet::parameterst::const_iterator parameter_it =
        declaration_parameters.begin();

      for(const exprt &called_arg : called_arguments)
      {
        if(parameter_it == declaration_parameters.end())
        {
          INVARIANT(
            code_type.has_ellipsis(), "Only case for insufficient args");
          break;
        }

        // Evaluate the expression that is being
        // passed into the function call (called_arg)
        abstract_object_pointert param_val =
          abstract_state.eval(called_arg, ns)->write_location_context(from);

        // Assign the evaluated value to the symbol associated with the
        // parameter of the function
        const symbol_exprt parameter_expr(
          parameter_it->get_identifier(), called_arg.type());
        abstract_state.assign(parameter_expr, param_val, ns);

        ++parameter_it;
      }

      // Too few arguments so invalid code
      DATA_INVARIANT(
        parameter_it == declaration_parameters.end(),
        "Number of arguments should match parameters");
    }
  }
  else
  {
    PRECONDITION(to == next);
    abstract_state.havoc("unknown opaque function call");
  }
}

bool variable_sensitivity_domaint::ignore_function_call_transform(
  const irep_idt &function_id) const
{
  static const std::set<irep_idt> ignored_internal_function = {
    CPROVER_PREFIX "set_must",
    CPROVER_PREFIX "get_must",
    CPROVER_PREFIX "set_may",
    CPROVER_PREFIX "get_may",
    CPROVER_PREFIX "cleanup",
    CPROVER_PREFIX "clear_may",
    CPROVER_PREFIX "clear_must"};

  return ignored_internal_function.find(function_id) !=
         ignored_internal_function.cend();
}

void variable_sensitivity_domaint::merge_three_way_function_return(
  const ai_domain_baset &function_call,
  const ai_domain_baset &function_start,
  const ai_domain_baset &function_end,
  const namespacet &ns)
{
  const variable_sensitivity_domaint &cast_function_call =
    static_cast<const variable_sensitivity_domaint &>(function_call);

  const variable_sensitivity_domaint &cast_function_start =
    static_cast<const variable_sensitivity_domaint &>(function_start);

  const variable_sensitivity_domaint &cast_function_end =
    static_cast<const variable_sensitivity_domaint &>(function_end);

  const std::vector<irep_idt> &modified_symbol_names =
    cast_function_start.get_modified_symbols(cast_function_end);

  std::vector<symbol_exprt> modified_symbols;
  modified_symbols.reserve(modified_symbol_names.size());
  std::transform(
    modified_symbol_names.begin(),
    modified_symbol_names.end(),
    std::back_inserter(modified_symbols),
    [&ns](const irep_idt &id) { return ns.lookup(id).symbol_expr(); });

  abstract_state = cast_function_call.abstract_state;
  apply_domain(modified_symbols, cast_function_end, ns);

  return;
}

void variable_sensitivity_domaint::apply_domain(
  std::vector<symbol_exprt> modified_symbols,
  const variable_sensitivity_domaint &source,
  const namespacet &ns)
{
  for(const auto &symbol : modified_symbols)
  {
    abstract_object_pointert value = source.abstract_state.eval(symbol, ns);
    abstract_state.assign(symbol, value, ns);
  }
}

void variable_sensitivity_domaint::assume(exprt expr, namespacet ns)
{
  ai_simplify(expr, ns);
  abstract_state.assume(expr, ns);
}

#ifdef ENABLE_STATS
abstract_object_statisticst
variable_sensitivity_domaint::gather_statistics(const namespacet &ns) const
{
  return abstract_state.gather_statistics(ns);
}
#endif
