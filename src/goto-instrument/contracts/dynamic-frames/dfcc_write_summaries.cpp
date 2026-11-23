/*******************************************************************\

Module: Dynamic frame condition checking

Author: Felipe R. Monteiro, felisous@amazon.com

\*******************************************************************/

#include "dfcc_write_summaries.h"

#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol.h>

#include "dfcc_is_cprover_symbol.h"

/// \p type, or the type its tag names.
static const typet &follow_tags(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_struct_tag)
    return ns.follow_tag(to_struct_tag_type(type));
  if(type.id() == ID_union_tag)
    return ns.follow_tag(to_union_tag_type(type));
  if(type.id() == ID_c_enum_tag)
    return ns.follow_tag(to_c_enum_tag_type(type));
  return type;
}

bool originst::merge(const originst &other)
{
  const std::size_t size = globals.size() + locals.size() + parameters.size();
  const bool was_unknown = unknown;
  globals.insert(other.globals.begin(), other.globals.end());
  locals.insert(other.locals.begin(), other.locals.end());
  parameters.insert(other.parameters.begin(), other.parameters.end());
  unknown |= other.unknown;
  return was_unknown != unknown ||
         size != globals.size() + locals.size() + parameters.size();
}

void write_summariest::compute(const std::vector<irep_idt> &roots)
{
  std::vector<irep_idt> work = roots;
  std::set<irep_idt> seen(roots.begin(), roots.end());
  while(!work.empty())
  {
    const irep_idt id = work.back();
    work.pop_back();
    functions.push_back(id);
    for(const auto &instruction : body_of(id).instructions)
    {
      if(
        instruction.is_function_call() &&
        instruction.call_function().id() == ID_symbol)
      {
        const irep_idt &callee =
          to_symbol_expr(instruction.call_function()).identifier();
        if(has_body(callee) && seen.insert(callee).second)
          work.push_back(callee);
      }
    }
  }
  // Iterate to a fixpoint for recursive functions: summaries only grow.
  bool changed = true;
  while(changed)
  {
    changed = false;
    for(const auto &id : functions)
    {
      write_summaryt summary = analyze(id);
      if(!(summary == summaries[id]))
      {
        summaries[id] = std::move(summary);
        changed = true;
      }
    }
  }
}

bool write_summariest::has_pointers(const typet &type)
{
  auto entry = pointer_types.find(type);
  if(entry != pointer_types.end())
    return entry->second;
  // This does not recurse into the base type of a pointer, and only a
  // pointer can make a type refer to itself, so this terminates.
  bool result = false;
  if(type.id() == ID_pointer)
    result = true;
  else if(
    type.id() == ID_struct_tag || type.id() == ID_union_tag ||
    type.id() == ID_c_enum_tag)
  {
    result = has_pointers(follow_tags(type, ns));
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &component : to_struct_union_type(type).components())
      result = result || has_pointers(component.type());
  }
  else if(type.id() == ID_array || type.id() == ID_vector)
    result = has_pointers(to_type_with_subtype(type).subtype());
  pointer_types[type] = result;
  return result;
}

bool write_summariest::has_body(const irep_idt &id) const
{
  auto entry = goto_functions.function_map.find(id);
  return entry != goto_functions.function_map.end() &&
         entry->second.body_available();
}

const goto_programt &write_summariest::body_of(const irep_idt &id) const
{
  return goto_functions.function_map.at(id).body;
}

bool write_summariest::is_global(const irep_idt &id) const
{
  const symbolt *symbol;
  return !ns.lookup(id, symbol) && symbol->is_static_lifetime;
}

write_summaryt write_summariest::analyze(const irep_idt &id)
{
  const goto_functiont &function = goto_functions.function_map.at(id);
  variables.clear();
  current = write_summaryt();
  for(std::size_t i = 0; i < function.parameter_identifiers.size(); ++i)
  {
    const irep_idt &parameter = function.parameter_identifiers[i];
    variables[parameter].parameters.insert(i);
  }
  do
  {
    variables_changed = false;
    for(const auto &instruction : function.body.instructions)
      analyze(instruction);
  } while(variables_changed);
  return current;
}

void write_summariest::analyze(const goto_programt::instructiont &instruction)
{
  if(instruction.is_assign())
    write(instruction.assign_lhs(), origins(instruction.assign_rhs()));
  else if(instruction.is_set_return_value())
    current.result.merge(origins(instruction.return_value()));
  else if(instruction.is_function_call())
    call(instruction);
  else if(instruction.is_other())
  {
    const codet &code = instruction.get_other();
    const irep_idt &statement = code.get_statement();
    if(
      statement == ID_array_set || statement == ID_array_copy ||
      statement == ID_array_replace || statement == ID_havoc_object)
    {
      originst content;
      content.unknown = true;
      write_through(origins(code.op0()), content);
    }
    else if(statement == ID_array_equal && code.operands().size() == 3)
    {
      // Assigns whether the arrays are equal to the third operand.
      write(code.op2(), originst{});
    }
    else if(
      statement == ID_expression || statement == ID_printf ||
      statement == ID_input || statement == ID_output ||
      statement == ID_nondet || statement == ID_asm || statement == ID_fence ||
      statement == ID_user_specified_predicate ||
      statement == ID_user_specified_parameter_predicates ||
      statement == ID_user_specified_return_predicates)
    {
      // These write nothing (symex ignores `asm`).
    }
    else
    {
      // Writes the analysis does not know about, for example `cpp_delete`.
      current.unknown = true;
    }
  }
}

void write_summariest::call(const goto_programt::instructiont &instruction)
{
  const exprt &function = instruction.call_function();
  const exprt &lhs = instruction.call_lhs();
  originst unknown;
  unknown.unknown = true;
  if(function.id() != ID_symbol)
  {
    current.unknown = true;
    if(lhs.is_not_nil())
      write(lhs, unknown);
    return;
  }
  const irep_idt &callee = to_symbol_expr(function).identifier();
  if(!has_body(callee))
  {
    // Built-ins write nothing but their result; any other function without
    // a body may write anything.
    if(!dfcc_is_cprover_function_symbol(callee))
      current.unknown = true;
    if(lhs.is_not_nil())
      write(lhs, unknown);
    return;
  }
  const write_summaryt summary = summaries[callee];
  const auto &arguments = instruction.call_arguments();
  current.globals.insert(summary.globals.begin(), summary.globals.end());
  current.unknown |= summary.unknown;
  for(const auto i : summary.parameters)
  {
    if(i < arguments.size())
      write_through(origins(arguments[i]), unknown);
    else
      current.unknown = true;
  }
  if(lhs.is_not_nil())
  {
    originst result;
    result.globals = summary.result.globals;
    result.unknown = summary.result.unknown || !summary.result.locals.empty();
    for(const auto i : summary.result.parameters)
    {
      if(i < arguments.size())
        result.merge(origins(arguments[i]));
      else
        result.unknown = true;
    }
    write(lhs, result);
  }
}

void write_summariest::write_through(
  const originst &target,
  const originst &content)
{
  current.globals.insert(target.globals.begin(), target.globals.end());
  current.parameters.insert(target.parameters.begin(), target.parameters.end());
  current.unknown |= target.unknown;
  for(const auto &local : target.locals)
    variables_changed |= variables[local].merge(content);
}

void write_summariest::write(const exprt &lhs, const originst &content)
{
  if(lhs.id() == ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(lhs).identifier();
    if(is_global(id))
      current.globals.insert(id);
    else
      variables_changed |= variables[id].merge(content);
  }
  else if(
    lhs.id() == ID_member || lhs.id() == ID_index ||
    lhs.id() == ID_byte_extract_little_endian ||
    lhs.id() == ID_byte_extract_big_endian || lhs.id() == ID_typecast)
  {
    const exprt &object = lhs.operands().front();
    // Writing a part of an object as another type, as through a member of a
    // union, may turn the bytes of a value without pointers, whose origins
    // the analysis does not track, into a pointer.
    const bool reinterprets =
      lhs.id() != ID_index &&
      (lhs.id() != ID_member || object.type().id() == ID_union ||
       object.type().id() == ID_union_tag);
    if(reinterprets && has_pointers(object.type()))
    {
      originst unknown;
      unknown.unknown = true;
      write(object, unknown);
    }
    else
      write(object, content);
  }
  else if(lhs.id() == ID_dereference)
    write_through(origins(to_dereference_expr(lhs).pointer()), content);
  else if(lhs.id() == ID_if)
  {
    write(to_if_expr(lhs).true_case(), content);
    write(to_if_expr(lhs).false_case(), content);
  }
  else
    current.unknown = true;
}

originst write_summariest::object_origins(const exprt &object)
{
  originst result;
  if(object.id() == ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(object).identifier();
    if(is_global(id))
      result.globals.insert(id);
    else
      result.locals.insert(id);
  }
  else if(
    object.id() == ID_member || object.id() == ID_index ||
    object.id() == ID_byte_extract_little_endian ||
    object.id() == ID_byte_extract_big_endian)
  {
    return object_origins(object.operands().front());
  }
  else if(object.id() == ID_dereference)
    return origins(to_dereference_expr(object).pointer());
  else if(object.id() == ID_string_constant || object.id() == ID_constant)
  {
  }
  else
    result.unknown = true;
  return result;
}

originst write_summariest::origins(const exprt &expr)
{
  originst result;
  if(expr.id() == ID_address_of)
    return object_origins(to_address_of_expr(expr).object());
  if(!has_pointers(expr.type()) && expr.id() != ID_typecast)
    return result;
  if(expr.id() == ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).identifier();
    if(is_global(id))
      result.unknown = true;
    else
      result = variables[id];
  }
  else if(expr.id() == ID_dereference)
  {
    // A value loaded from memory: from the analysis' locals, or unknown.
    const originst target = origins(to_dereference_expr(expr).pointer());
    result.unknown =
      target.unknown || !target.globals.empty() || !target.parameters.empty();
    for(const auto &local : target.locals)
      result.merge(variables[local]);
  }
  else if(expr.id() == ID_typecast)
  {
    const exprt &op = to_typecast_expr(expr).op();
    if(!has_pointers(expr.type()))
      return result;
    // A pointer made from an integer may point anywhere.
    if(!has_pointers(op.type()))
      result.unknown = true;
    else
    {
      result = origins(op);
      if(expr.type().id() == ID_pointer && op.type().id() == ID_pointer)
      {
        // Accessing the locals that the pointer points to as another type
        // may read or write the bytes of a value without pointers, whose
        // origins the analysis does not track, as a pointer.
        const typet &base_type = to_pointer_type(expr.type()).base_type();
        if(
          base_type.id() != ID_empty &&
          base_type != to_pointer_type(op.type()).base_type())
        {
          originst unknown;
          unknown.unknown = true;
          for(const auto &local : result.locals)
            variables_changed |= variables[local].merge(unknown);
        }
      }
    }
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    // As above, reading an object as another type may make a pointer of
    // the bytes of a value without pointers.
    const exprt &op = to_byte_extract_expr(expr).op();
    if(op.type() == expr.type())
      result = origins(op);
    else
      result.unknown = true;
  }
  else if(
    expr.id() == ID_union || expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian ||
    (expr.id() == ID_with &&
     (expr.type().id() == ID_union || expr.type().id() == ID_union_tag)))
  {
    // A member of a union, or an update of the bytes of an object, may hold
    // a value without pointers that is read as a pointer.
    result.unknown = true;
  }
  else if(expr.id() == ID_constant || expr.id() == ID_nil)
  {
  }
  else if(expr.id() == ID_if)
  {
    result = origins(to_if_expr(expr).true_case());
    result.merge(origins(to_if_expr(expr).false_case()));
  }
  else if(expr.id() == ID_side_effect || expr.id() == ID_nondet_symbol)
    result.unknown = true;
  else
  {
    // Member and index of a value, pointer arithmetic, `with`, struct
    // literals...: the pointers in the result come from the operands.
    for(const auto &op : expr.operands())
      result.merge(origins(op));
  }
  return result;
}

/// Appends a write of a nondeterministic value to the object \p pointer
/// points to, for each pointer in the value of \p value. Returns false if
/// it cannot find them all.
static bool write_through(
  const exprt &value,
  write_summariest &summaries,
  const namespacet &ns,
  const source_locationt &location,
  goto_programt &body)
{
  const typet &type = value.type();
  if(type.id() == ID_pointer)
  {
    const typet &pointee = to_pointer_type(type).base_type();
    const bool sized = pointee.id() != ID_empty && pointee.id() != ID_code &&
                       !(pointee.id() == ID_struct_tag &&
                         follow_tags(pointee, ns).get_bool(ID_incomplete));
    const exprt pointer =
      sized ? value : exprt(typecast_exprt(value, pointer_type(char_type())));
    const dereference_exprt target(pointer);
    body.add(goto_programt::make_assignment(
      target, side_effect_expr_nondett(target.type(), location), location));
    return true;
  }
  if(!summaries.has_pointers(type))
    return true;
  if(type.id() == ID_struct_tag || type.id() == ID_struct)
  {
    for(const auto &component :
        to_struct_type(follow_tags(type, ns)).components())
    {
      if(!write_through(
           member_exprt(value, component), summaries, ns, location, body))
      {
        return false;
      }
    }
    return true;
  }
  return false;
}

/// The summary body of \p id. Returns false if it should keep its body.
static bool make_body(
  const irep_idt &id,
  const goto_functiont &function,
  const write_summaryt &summary,
  write_summariest &summaries,
  const namespacet &ns,
  goto_programt &body)
{
  if(summary.unknown)
    return false;
  const symbolt &symbol = ns.lookup(id);
  const source_locationt &location = symbol.location;
  for(const auto &global : summary.globals)
  {
    const symbol_exprt target = ns.lookup(global).symbol_expr();
    body.add(goto_programt::make_assignment(
      target, side_effect_expr_nondett(target.type(), location), location));
  }
  for(const auto i : summary.parameters)
  {
    INVARIANT(
      i < function.parameter_identifiers.size(),
      "summaries only name parameters of the function");
    const symbol_exprt parameter =
      ns.lookup(function.parameter_identifiers[i]).symbol_expr();
    if(!write_through(parameter, summaries, ns, location, body))
      return false;
  }
  const typet &return_type = to_code_type(symbol.type).return_type();
  if(return_type.id() != ID_empty)
  {
    exprt result = side_effect_expr_nondett(return_type, location);
    if(return_type.id() == ID_pointer && !summary.result.unknown)
    {
      // Choose among the objects the result may point into.
      std::vector<exprt> candidates;
      for(const auto &global : summary.result.globals)
      {
        candidates.push_back(typecast_exprt::conditional_cast(
          address_of_exprt(ns.lookup(global).symbol_expr()), return_type));
      }
      for(const auto i : summary.result.parameters)
      {
        INVARIANT(
          i < function.parameter_identifiers.size(),
          "summaries only name parameters of the function");
        const symbol_exprt parameter =
          ns.lookup(function.parameter_identifiers[i]).symbol_expr();
        if(parameter.type().id() != ID_pointer)
          return false;
        candidates.push_back(
          typecast_exprt::conditional_cast(parameter, return_type));
      }
      for(const auto &candidate : candidates)
      {
        result = if_exprt(
          side_effect_expr_nondett(bool_typet(), location), candidate, result);
      }
    }
    else if(summaries.has_pointers(return_type))
    {
      // A result whose pointers the summary cannot name.
      return false;
    }
    body.add(goto_programt::make_set_return_value(result, location));
  }
  body.add(goto_programt::make_end_function(location));
  return true;
}

/// The functions with a body in \p goto_functions that \p program may call,
/// directly or through the functions it calls, and that DFCC does not
/// instrument.
static std::vector<irep_idt> uninstrumented_callees(
  const goto_functionst &goto_functions,
  const goto_programt &program)
{
  std::vector<irep_idt> result;
  std::set<irep_idt> seen;
  std::vector<const goto_programt *> work{&program};
  while(!work.empty())
  {
    const goto_programt &body = *work.back();
    work.pop_back();
    for(const auto &instruction : body.instructions)
    {
      if(
        !instruction.is_function_call() ||
        instruction.call_function().id() != ID_symbol)
      {
        continue;
      }
      const irep_idt &callee =
        to_symbol_expr(instruction.call_function()).identifier();
      const auto entry = goto_functions.function_map.find(callee);
      if(
        entry == goto_functions.function_map.end() ||
        !entry->second.body_available() || !seen.insert(callee).second)
      {
        continue;
      }
      if(dfcc_is_cprover_function_symbol(callee))
        result.push_back(callee);
      work.push_back(&entry->second.body);
    }
  }
  return result;
}

write_summary_bodiest::write_summary_bodiest(
  goto_functionst &goto_functions,
  const goto_programt &program,
  const namespacet &ns)
  : goto_functions(goto_functions)
{
  const std::vector<irep_idt> roots =
    uninstrumented_callees(goto_functions, program);
  write_summariest summaries(goto_functions, ns);
  summaries.compute(roots);
  for(const auto &id : roots)
  {
    goto_functiont &function = goto_functions.function_map.at(id);
    goto_programt body;
    if(make_body(id, function, summaries[id], summaries, ns, body))
    {
      saved.emplace_back(id, std::move(function.body));
      function.body = std::move(body);
    }
  }
}

write_summary_bodiest::~write_summary_bodiest()
{
  for(auto &entry : saved)
    goto_functions.function_map.at(entry.first).body = std::move(entry.second);
}
