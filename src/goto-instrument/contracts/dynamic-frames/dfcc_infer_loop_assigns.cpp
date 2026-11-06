/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/
#include "dfcc_infer_loop_assigns.h"

#include <util/c_types.h>
#include <util/find_symbols.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <goto-programs/goto_inline.h>

#include <analyses/local_may_alias.h>
#include <goto-instrument/contracts/utils.h>

#include "dfcc_is_cprover_symbol.h"
#include "dfcc_loop_nesting_graph.h"
#include "dfcc_root_object.h"

/// Builds a call expression `object_whole(expr)`
static exprt
make_object_whole_call_expr(const exprt &expr, const namespacet &ns)
{
  const symbolt &object_whole_sym = ns.lookup(CPROVER_PREFIX "object_whole");
  const code_typet &object_whole_code_type =
    to_code_type(object_whole_sym.type);
  return side_effect_expr_function_callt(
    object_whole_sym.symbol_expr(),
    {{expr}},
    object_whole_code_type.return_type(),
    expr.source_location());
}

/// Returns true iff \p expr contains at least one identifier found in
/// \p identifiers.
static bool
depends_on(const exprt &expr, std::unordered_set<irep_idt> identifiers)
{
  const std::unordered_set<irep_idt> ids = find_symbol_identifiers(expr);
  for(const auto &id : ids)
  {
    if(identifiers.find(id) != identifiers.end())
      return true;
  }
  return false;
}

/// Collect identifiers that are local to this loop.
/// A variable is a loop local if and only if it is declared inside the loop
/// (i.e., there is a DECL instruction for it in the loop body).  Variables
/// declared outside the loop are never considered loop locals, even when they
/// are only read or written inside the loop, because their storage persists
/// across iterations and they must be havoced to ensure soundness.
std::unordered_set<irep_idt> gen_loop_locals_set(
  goto_functiont &goto_function,
  const dfcc_loop_nesting_graph_nodet &loop_node)
{
  std::unordered_set<irep_idt> loop_locals;

  const auto &loop = loop_node.instructions;

  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    // Only variables declared inside the loop are loop locals.
    if(i_it->is_decl() && loop.contains(i_it))
    {
      loop_locals.insert(i_it->decl_symbol().identifier());
    }
  }

  return loop_locals;
}

/// Find all identifiers in `src`.
static std::unordered_set<irep_idt>
find_symbol_identifiers(const goto_programt &src)
{
  std::unordered_set<irep_idt> identifiers;
  for(const auto &instruction : src.instructions)
  {
    // compute forward edges first
    switch(instruction.type())
    {
    case ASSERT:
    case ASSUME:
    case GOTO:
      find_symbols(instruction.condition(), identifiers);
      break;

    case FUNCTION_CALL:
      find_symbols(instruction.call_lhs(), identifiers);
      for(const auto &e : instruction.call_arguments())
        find_symbols(e, identifiers);
      break;
    case ASSIGN:
    case OTHER:

    case SET_RETURN_VALUE:
    case DECL:
    case DEAD:
      for(const auto &e : instruction.code().operands())
      {
        find_symbols(e, identifiers);
      }
      break;

    case END_THREAD:
    case END_FUNCTION:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
    case SKIP:
    case LOCATION:
    case CATCH:
    case THROW:
    case START_THREAD:
      break;
    case NO_INSTRUCTION_TYPE:
    case INCOMPLETE_GOTO:
      UNREACHABLE;
      break;
    }
  }
  return identifiers;
}

/// Infer loop assigns in the given `loop`. Loop assigns should depend
/// on some identifiers in `candidate_targets`. `function_assigns_map`
/// contains the function contracts used to infer loop assigns of
/// function_call instructions.
static assignst dfcc_infer_loop_assigns_for_loop(
  const local_may_aliast &local_may_alias,
  goto_functiont &goto_function,
  const dfcc_loop_nesting_graph_nodet &loop,
  const std::unordered_set<irep_idt> &candidate_targets,
  message_handlert &message_handler,
  const namespacet &ns)
{
  // infer
  assignst assigns;
  infer_loop_assigns(local_may_alias, loop.instructions, assigns);

  // compute locals
  std::unordered_set<irep_idt> loop_locals =
    gen_loop_locals_set(goto_function, loop);

  // widen or drop targets that depend on loop-locals or are non-constant,
  // ie. depend on other locations assigned by the loop.
  // e.g: if the loop assigns {i, a[i]}, then a[i] is non-constant.
  havoc_utils_can_forward_propagatet is_constant(assigns, ns);
  assignst result;
  for(const auto &expr : assigns)
  {
    // Skip targets that only depend on non-visible identifiers.
    if(!depends_on(expr, candidate_targets))
    {
      continue;
    }

    if(depends_on(expr, loop_locals))
    {
      // Target depends on loop locals, attempt widening to the root object
      auto root_objects = dfcc_root_objects(expr);
      for(const auto &root_object : root_objects)
      {
        if(!depends_on(root_object, loop_locals))
        {
          address_of_exprt address_of_root_object(root_object);
          address_of_root_object.add_source_location() =
            root_object.source_location();
          result.emplace(
            make_object_whole_call_expr(address_of_root_object, ns));
        }
      }
    }
    else
    {
      address_of_exprt address_of_expr(expr);
      address_of_expr.add_source_location() = expr.source_location();
      // Widen assigns targets to object_whole if `expr` is a dereference or
      // with constant address.
      if(expr.id() == ID_dereference || !is_constant(address_of_expr))
      {
        // Target address is not constant, widening to the whole object
        result.emplace(make_object_whole_call_expr(address_of_expr, ns));
      }
      else
      {
        result.emplace(expr);
      }
    }
  }

  return result;
}

namespace
{
/// \p type, or the type its tag names.
const typet &follow_tags(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_struct_tag)
    return ns.follow_tag(to_struct_tag_type(type));
  if(type.id() == ID_union_tag)
    return ns.follow_tag(to_union_tag_type(type));
  if(type.id() == ID_c_enum_tag)
    return ns.follow_tag(to_c_enum_tag_type(type));
  return type;
}

/// The objects a pointer-valued expression of a function may point into,
/// flow-insensitively: globals, locals of the function (including its
/// parameter variables), the objects its parameters point to on entry, or
/// objects the analysis cannot name (`unknown`).
struct originst
{
  std::set<irep_idt> globals;
  std::set<irep_idt> locals;
  std::set<std::size_t> parameters;
  bool unknown = false;

  /// Add \p other to this. Returns true if this changed.
  bool merge(const originst &other)
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
};

/// What a function, its callees included, may write outside its own locals,
/// and what its result may point to.
struct write_summaryt
{
  /// Globals it may write, whole.
  std::set<irep_idt> globals;
  /// Parameters through which it may write, into the whole object they point
  /// to on entry.
  std::set<std::size_t> parameters;
  /// It may write through a pointer whose target the analysis cannot name.
  bool unknown = false;
  originst result;

  bool operator==(const write_summaryt &other) const
  {
    return globals == other.globals && parameters == other.parameters &&
           unknown == other.unknown && result.globals == other.result.globals &&
           result.locals == other.result.locals &&
           result.parameters == other.result.parameters &&
           result.unknown == other.result.unknown;
  }
};

/// Computes `write_summaryt`s, flow-insensitively, over the bodies in a
/// `goto_functionst`.
class write_summariest
{
public:
  write_summariest(const goto_functionst &goto_functions, const namespacet &ns)
    : goto_functions(goto_functions), ns(ns)
  {
  }

  /// The summaries of \p roots and of every function they call, transitively.
  void compute(const std::vector<irep_idt> &roots)
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

  const write_summaryt &operator[](const irep_idt &id)
  {
    return summaries[id];
  }

  bool has_pointers(const typet &type)
  {
    auto entry = pointer_types.find(type);
    if(entry != pointer_types.end())
      return entry->second;
    // Assume none while the type is visited, for recursive types.
    pointer_types[type] = false;
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

private:
  const goto_functionst &goto_functions;
  const namespacet &ns;
  std::vector<irep_idt> functions;
  std::map<irep_idt, write_summaryt> summaries;
  std::unordered_map<typet, bool, irep_hash> pointer_types;

  // State of the function being analyzed.
  std::map<irep_idt, originst> variables;
  std::map<irep_idt, std::size_t> parameter_index;
  write_summaryt current;
  bool variables_changed = false;

  bool has_body(const irep_idt &id) const
  {
    auto entry = goto_functions.function_map.find(id);
    return entry != goto_functions.function_map.end() &&
           entry->second.body_available();
  }

  const goto_programt &body_of(const irep_idt &id) const
  {
    return goto_functions.function_map.at(id).body;
  }

  bool is_global(const irep_idt &id) const
  {
    const symbolt *symbol;
    return !ns.lookup(id, symbol) && symbol->is_static_lifetime;
  }

  write_summaryt analyze(const irep_idt &id)
  {
    const goto_functiont &function = goto_functions.function_map.at(id);
    variables.clear();
    parameter_index.clear();
    current = write_summaryt();
    for(std::size_t i = 0; i < function.parameter_identifiers.size(); ++i)
    {
      const irep_idt &parameter = function.parameter_identifiers[i];
      parameter_index[parameter] = i;
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

  void analyze(const goto_programt::instructiont &instruction)
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
    }
  }

  void call(const goto_programt::instructiont &instruction)
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

  /// Records that \p content may be written into the objects of \p target.
  void write_through(const originst &target, const originst &content)
  {
    current.globals.insert(target.globals.begin(), target.globals.end());
    current.parameters.insert(
      target.parameters.begin(), target.parameters.end());
    current.unknown |= target.unknown;
    for(const auto &local : target.locals)
      variables_changed |= variables[local].merge(content);
  }

  /// Records an assignment of \p content to \p lhs.
  void write(const exprt &lhs, const originst &content)
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
      write(lhs.operands().front(), content);
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

  /// The objects whose address is `&object`.
  originst object_origins(const exprt &object)
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

  /// The objects the pointers in the value of \p expr may point into.
  originst origins(const exprt &expr)
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
        result = origins(op);
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
};

/// While it lives, replaces the body of each function that DFCC does not
/// instrument (`dfcc_is_cprover_function_symbol`) by a summary of its writes,
/// so that inlining it into the copy that the inference works on is cheap:
/// a tool may instrument every instruction of a loop with calls to such
/// functions (for example Kani's aliasing checks), and inlining their bodies
/// can then run out of memory. Their writes are not checked against a write
/// set, but the objects they write must still be havocked, so the summary
/// writes a nondeterministic value to:
/// - each global the function or its callees may write, whole;
/// - the whole object each pointer parameter it may write through points to;
/// - its result, which may point to the objects its result may point to.
/// A function that may write through a pointer the summary cannot name keeps
/// its body. The bodies are restored on destruction.
class write_summary_bodiest
{
public:
  write_summary_bodiest(goto_functionst &goto_functions, const namespacet &ns)
    : goto_functions(goto_functions)
  {
    std::vector<irep_idt> roots;
    for(const auto &entry : goto_functions.function_map)
    {
      if(
        dfcc_is_cprover_function_symbol(entry.first) &&
        entry.second.body_available())
      {
        roots.push_back(entry.first);
      }
    }
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

  ~write_summary_bodiest()
  {
    for(auto &entry : saved)
      goto_functions.function_map.at(entry.first).body =
        std::move(entry.second);
  }

private:
  goto_functionst &goto_functions;
  std::vector<std::pair<irep_idt, goto_programt>> saved;

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
      if(i >= function.parameter_identifiers.size())
        return false;
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
          if(i >= function.parameter_identifiers.size())
            return false;
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
            side_effect_expr_nondett(bool_typet(), location),
            candidate,
            result);
        }
      }
      else if(summaries.has_pointers(return_type) || summary.result.unknown)
      {
        // A result whose pointers the summary cannot name.
        if(summaries.has_pointers(return_type))
          return false;
      }
      body.add(goto_programt::make_set_return_value(result, location));
    }
    body.add(goto_programt::make_end_function(location));
    return true;
  }
};
} // namespace

/// Remove assignments to `__CPROVER_dead_object` to avoid aliasing all targets
/// that are assigned to `__CPROVER_dead_object`.
static void remove_dead_object_assignment(goto_functiont &goto_function)
{
  Forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_assign())
    {
      auto &lhs = i_it->assign_lhs();

      if(
        lhs.id() == ID_symbol &&
        to_symbol_expr(lhs).identifier() == CPROVER_PREFIX "dead_object")
      {
        i_it->turn_into_skip();
      }
    }
  }
}

void dfcc_infer_loop_assigns_for_function(
  std::map<std::size_t, assignst> &inferred_loop_assigns_map,
  goto_functionst &goto_functions,
  const goto_functiont &goto_function,
  message_handlert &message_handler,
  const namespacet &ns)
{
  messaget log(message_handler);

  // Collect all candidate targets---identifiers visible in `goto_function`.
  const auto candidate_targets = find_symbol_identifiers(goto_function.body);

  // We infer loop assigns based on the copy of `goto_function`.
  goto_functiont goto_function_copy;
  goto_function_copy.copy_from(goto_function);

  // Build the loop id map before inlining attempt. So that we can later
  // distinguish loops in the original body and loops added by inlining.
  const auto loop_nesting_graph =
    build_loop_nesting_graph(goto_function_copy.body);
  auto topsorted = loop_nesting_graph.topsort();
  // skip function without loop.
  if(topsorted.empty())
    return;

  // Map from targett in `goto_function_copy` to loop number.
  std::
    unordered_map<goto_programt::const_targett, std::size_t, const_target_hash>
      loop_number_map;

  for(const auto id : topsorted)
  {
    loop_number_map.emplace(
      loop_nesting_graph[id].head, loop_nesting_graph[id].latch->loop_number);
  }

  // We avoid inlining `malloc` and `free` whose variables are not assigns.
  auto malloc_body = goto_functions.function_map.extract(irep_idt("malloc"));
  auto free_body = goto_functions.function_map.extract(irep_idt("free"));

  // Replace the bodies of the functions that DFCC does not instrument by
  // summaries of their writes, see `write_summary_bodiest`.
  write_summary_bodiest summary_bodies(goto_functions, ns);

  // Inline all function calls in goto_function_copy; this is best-effort
  // inlining, we can safely ignore warnings here.
  null_message_handlert null_message_handler;
  goto_program_inline(
    goto_functions, goto_function_copy.body, ns, null_message_handler);
  // Update the body to make sure all goto correctly jump to valid targets.
  goto_function_copy.body.update();
  // Build the loop graph after inlining.
  const auto inlined_loop_nesting_graph =
    build_loop_nesting_graph(goto_function_copy.body);

  // Alias analysis.
  remove_dead_object_assignment(goto_function_copy);
  local_may_aliast local_may_alias(goto_function_copy);

  auto inlined_topsorted = inlined_loop_nesting_graph.topsort();

  for(const auto inlined_id : inlined_topsorted)
  {
    // We only infer loop assigns for loops in the original function.
    if(
      loop_number_map.find(inlined_loop_nesting_graph[inlined_id].head) !=
      loop_number_map.end())
    {
      const auto loop_number =
        loop_number_map[inlined_loop_nesting_graph[inlined_id].head];
      const auto inlined_loop = inlined_loop_nesting_graph[inlined_id];

      inferred_loop_assigns_map[loop_number] = dfcc_infer_loop_assigns_for_loop(
        local_may_alias,
        goto_function_copy,
        inlined_loop,
        candidate_targets,
        message_handler,
        ns);
    }
  }
  // Restore the function boyd of `malloc` and `free`.
  goto_functions.function_map.insert(std::move(malloc_body));
  goto_functions.function_map.insert(std::move(free_body));
}
