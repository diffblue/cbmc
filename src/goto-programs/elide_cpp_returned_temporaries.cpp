/*******************************************************************\

Module: Elide C++ returned temporaries (guaranteed copy elision)

Author: Kiro

\*******************************************************************/

/// \file
/// Lower by-value returns of non-POD C++ class types to
/// construct-into-caller-storage (N5008 [class.copy.elis],
/// [stmt.return]/2).

#include "elide_cpp_returned_temporaries.h"

#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/replace_symbol.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include "goto_model.h"

#include <set>

/// Collect the identifiers of the class types that have a constructor
/// or destructor symbol.  A C++ class return type needs the elision
/// lowering iff relocating the object bitwise is not valid, i.e. the
/// type is not trivially copyable ([class.prop],
/// [basic.types.general]/2: only trivially copyable types may be
/// copied as bytes).  The C++ front end synthesizes
/// constructor/destructor symbols for exactly the non-POD classes (its
/// POD notion approximates trivial copyability), so the existence of
/// such a symbol -- recognizable by its return type and `this`
/// parameter -- identifies the types whose returns must be lowered.
static std::set<irep_idt>
classes_with_special_member_functions(const symbol_table_baset &symbol_table)
{
  std::set<irep_idt> result;

  for(const auto &named_symbol : symbol_table.symbols)
  {
    const symbolt &symbol = named_symbol.second;
    if(symbol.mode != ID_cpp || symbol.type.id() != ID_code)
      continue;

    const code_typet &code_type = to_code_type(symbol.type);
    const irep_idt &rt_id = code_type.return_type().id();
    if(rt_id != ID_constructor && rt_id != ID_destructor)
      continue;

    if(code_type.parameters().empty())
      continue;

    const typet &this_type = code_type.parameters().front().type();
    if(
      this_type.id() == ID_pointer &&
      to_pointer_type(this_type).base_type().id() == ID_struct_tag)
    {
      result.insert(to_struct_tag_type(to_pointer_type(this_type).base_type())
                      .get_identifier());
    }
  }

  return result;
}

/// Find the destructor symbol of the class named by \p struct_tag, if
/// any, and return its symbol expression.
static std::optional<symbol_exprt>
find_destructor(const typet &struct_tag, const symbol_table_baset &symbol_table)
{
  const irep_idt &class_id = to_struct_tag_type(struct_tag).get_identifier();

  for(const auto &named_symbol : symbol_table.symbols)
  {
    const symbolt &symbol = named_symbol.second;
    if(symbol.mode != ID_cpp || symbol.type.id() != ID_code)
      continue;

    const code_typet &code_type = to_code_type(symbol.type);
    if(
      code_type.return_type().id() != ID_destructor ||
      code_type.parameters().size() != 1)
    {
      continue;
    }

    const typet &this_type = code_type.parameters().front().type();
    if(
      this_type.id() == ID_pointer &&
      to_pointer_type(this_type).base_type().id() == ID_struct_tag &&
      to_struct_tag_type(to_pointer_type(this_type).base_type())
          .get_identifier() == class_id)
    {
      return symbol_exprt{symbol.name, symbol.type};
    }
  }

  return {};
}

/// Find a relocating constructor of the class named by \p struct_tag: with
/// \p allow_move, the move constructor if present, the copy constructor
/// otherwise.  At this level references are pointers; the move constructor
/// is the two-parameter constructor whose second parameter is an
/// rvalue-reference to the class ([class.copy.ctor]/1-2).
static std::optional<symbol_exprt> find_relocating_constructor(
  const typet &struct_tag,
  const symbol_table_baset &symbol_table,
  bool allow_move)
{
  const irep_idt &class_id = to_struct_tag_type(struct_tag).get_identifier();

  std::optional<symbol_exprt> copy_constructor;

  for(const auto &named_symbol : symbol_table.symbols)
  {
    const symbolt &symbol = named_symbol.second;
    if(symbol.mode != ID_cpp || symbol.type.id() != ID_code)
      continue;

    const code_typet &code_type = to_code_type(symbol.type);
    if(
      code_type.return_type().id() != ID_constructor ||
      code_type.parameters().size() != 2)
    {
      continue;
    }

    auto param_class = [&](const typet &t) -> bool
    {
      return t.id() == ID_pointer &&
             to_pointer_type(t).base_type().id() == ID_struct_tag &&
             to_struct_tag_type(to_pointer_type(t).base_type())
                 .get_identifier() == class_id;
    };

    if(!param_class(code_type.parameters().front().type()))
      continue;

    const typet &source_type = code_type.parameters().back().type();
    if(!param_class(source_type))
      continue;

    if(is_rvalue_reference(source_type))
    {
      if(allow_move)
        return symbol_exprt{symbol.name, symbol.type};
    }
    else
      copy_constructor = symbol_exprt{symbol.name, symbol.type};
  }

  return copy_constructor;
}

/// Is \p instruction a call to a destructor whose single argument is
/// the address of \p object?
static bool is_destructor_call_on(
  const goto_programt::instructiont &instruction,
  const symbol_exprt &object)
{
  if(!instruction.is_function_call())
    return false;

  const exprt &function = instruction.call_function();
  if(function.id() != ID_symbol)
    return false;

  if(
    to_code_type(function.type()).return_type().id() != ID_destructor ||
    instruction.call_arguments().size() != 1)
  {
    return false;
  }

  const exprt &arg = skip_typecast(instruction.call_arguments().front());
  return arg.id() == ID_address_of &&
         to_address_of_expr(arg).object() == object;
}

/// Does \p expr contain a reference to the symbol \p identifier?
static bool contains_symbol(const exprt &expr, const irep_idt &identifier)
{
  if(
    expr.id() == ID_symbol &&
    to_symbol_expr(expr).get_identifier() == identifier)
    return true;
  for(const auto &op : expr.operands())
    if(contains_symbol(op, identifier))
      return true;
  return false;
}

/// Rewrite the body of a lowered function: for each SET RETURN VALUE of
/// a front-end return temporary, substitute that temporary instance by
/// the hidden result parameter's pointee so the returned object is
/// constructed directly into the caller's storage ([class.copy.elis]/1:
/// the temporary and the function's result object are the same object).
/// The temporary's declaration, liveness markers and post-return
/// destructor call are dropped: the result object's storage and
/// lifetime are the caller's, which also destroys it.
///
/// The front end reuses temporary identifiers (several unrelated
/// temporaries in one function may all be named `$tmp::tmp_obj`), so
/// the substitution is confined to the returned instance's live range:
/// from the closest preceding DECL of the symbol to the next DECL of
/// the same symbol (or the end of the body).  Front-end-emitted code
/// keeps an instance's references between these bounds in instruction
/// order.
static void lower_returns_in_body(
  goto_programt &body,
  const symbol_exprt &result_parameter,
  const irep_idt &function_id,
  const symbol_table_baset &symbol_table)
{
  const dereference_exprt result_object{result_parameter};

  auto &instructions = body.instructions;

  for(auto set_rv_it = instructions.begin(); set_rv_it != instructions.end();
      ++set_rv_it)
  {
    if(!set_rv_it->is_set_return_value())
      continue;

    const exprt &value = skip_typecast(set_rv_it->return_value());

    if(
      value.id() != ID_symbol ||
      id2string(to_symbol_expr(value).get_identifier()).find("::$tmp::") ==
        std::string::npos)
    {
      // Returned values that are not front-end return temporaries (the
      // front end returns a named local directly when it applies NRVO).
      // Not eliding here is conforming ([class.copy.elis]/1 elision of a
      // named object is optional); initialize the result object with a
      // constructor call instead.  Per [class.copy.elis]/3 the operand
      // is treated as an rvalue -- selecting the move constructor --
      // only when it names an implicitly movable entity: a non-volatile
      // object with automatic storage duration declared in the function
      // (at this level: a symbol scoped to the function; `return s;`
      // where s is a reference parameter dereferences the pointer and
      // must COPY, since the referent is not owned by this function).
      // The operand's own destructor call after the return correctly
      // destroys the copied/moved-from object where one exists.
      const bool implicitly_movable =
        value.id() == ID_symbol &&
        id2string(to_symbol_expr(value).get_identifier())
            .compare(
              0,
              id2string(function_id).size() + 2,
              id2string(function_id) + "::") == 0;

      const auto relocating_constructor =
        value.type().id() == ID_struct_tag
          ? find_relocating_constructor(
              value.type(), symbol_table, implicitly_movable)
          : std::optional<symbol_exprt>{};

      auto labels = std::move(set_rv_it->labels);

      if(relocating_constructor.has_value())
      {
        code_function_callt constructor_call{
          *relocating_constructor,
          {address_of_exprt{result_object},
           address_of_exprt{skip_typecast(set_rv_it->return_value())}}};
        const source_locationt location = set_rv_it->source_location();
        set_rv_it->clear(goto_program_instruction_typet::FUNCTION_CALL);
        *set_rv_it =
          goto_programt::make_function_call(constructor_call, location);
      }
      else
      {
        // no relocating constructor: the type is trivially copyable
        code_assignt assignment{result_object, set_rv_it->return_value()};
        set_rv_it->clear(goto_program_instruction_typet::ASSIGN);
        set_rv_it->code_nonconst() = std::move(assignment);
      }

      set_rv_it->labels = std::move(labels);
      continue;
    }

    const symbol_exprt temporary = to_symbol_expr(value);
    const irep_idt &temporary_id = temporary.get_identifier();

    // instance live range: closest preceding DECL .. next DECL/end
    auto range_begin = instructions.begin();
    for(auto it = instructions.begin(); it != set_rv_it; ++it)
      if(it->is_decl() && it->decl_symbol().get_identifier() == temporary_id)
        range_begin = it;

    auto range_end = std::next(set_rv_it);
    while(range_end != instructions.end() &&
          !(range_end->is_decl() &&
            range_end->decl_symbol().get_identifier() == temporary_id))
    {
      ++range_end;
    }

    unchecked_replace_symbolt replace;
    replace.insert(temporary, result_object);

    for(auto it = range_begin; it != range_end; ++it)
    {
      if(it == set_rv_it)
      {
        it->turn_into_skip();
        continue;
      }

      // The temporary's storage becomes the caller's: drop its
      // declaration and death, its end-of-life marker, and its
      // destructor call.
      if(
        (it->is_decl() && it->decl_symbol().get_identifier() == temporary_id) ||
        (it->is_dead() && it->dead_symbol().get_identifier() == temporary_id))
      {
        it->turn_into_skip();
        continue;
      }

      if(
        it->is_assign() && it->assign_lhs().id() == ID_symbol &&
        to_symbol_expr(it->assign_lhs()).get_identifier() == CPROVER_PREFIX
          "dead_object" &&
        contains_symbol(it->assign_rhs(), temporary_id))
      {
        it->turn_into_skip();
        continue;
      }

      if(is_destructor_call_on(*it, temporary))
      {
        it->turn_into_skip();
        continue;
      }

      it->transform(
        [&replace](exprt e) -> std::optional<exprt>
        {
          // replace() returns true when nothing was replaced
          if(replace.replace(e))
            return {};
          return e;
        });
    }
  }
}

void elide_cpp_returned_temporaries(goto_modelt &goto_model)
{
  symbol_table_baset &symbol_table = goto_model.symbol_table;
  const namespacet ns(symbol_table);

  const std::set<irep_idt> special_member_classes =
    classes_with_special_member_functions(symbol_table);

  // Collect the functions to lower: C++ functions with a body whose
  // return type is a non-trivially-copyable class.  Bodyless stubs keep
  // their signature (there is no returned temporary to elide).
  std::set<irep_idt> lowered;

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
      continue;

    const symbolt &function_symbol = ns.lookup(gf_entry.first);
    if(function_symbol.mode != ID_cpp)
      continue;

    const code_typet &code_type = to_code_type(function_symbol.type);
    const typet &return_type = code_type.return_type();
    if(
      return_type.id() == ID_struct_tag &&
      special_member_classes.count(
        to_struct_tag_type(return_type).get_identifier()))
    {
      lowered.insert(gf_entry.first);
    }
  }

  if(lowered.empty())
    return;

  // Rewrite the lowered functions' signatures and bodies.
  for(const irep_idt &function_id : lowered)
  {
    symbolt &function_symbol = symbol_table.get_writeable_ref(function_id);
    code_typet code_type = to_code_type(function_symbol.type);

    const pointer_typet result_pointer_type =
      pointer_type(code_type.return_type());

    // hidden result parameter, appended after the declared parameters
    symbolt &parameter_symbol = get_fresh_aux_symbol(
      result_pointer_type,
      id2string(function_id),
      "#result",
      function_symbol.location,
      function_symbol.mode,
      symbol_table);
    parameter_symbol.is_parameter = true;
    parameter_symbol.is_lvalue = true;
    parameter_symbol.is_thread_local = true;
    parameter_symbol.is_file_local = true;
    parameter_symbol.is_state_var = true;

    code_typet::parametert result_parameter{result_pointer_type};
    result_parameter.set_identifier(parameter_symbol.name);
    result_parameter.set_base_name(parameter_symbol.base_name);
    code_type.parameters().push_back(result_parameter);
    code_type.return_type() = empty_typet{};
    function_symbol.type = code_type;

    auto &goto_function =
      goto_model.goto_functions.function_map.at(function_id);
    goto_function.parameter_identifiers.push_back(parameter_symbol.name);

    lower_returns_in_body(
      goto_function.body,
      parameter_symbol.symbol_expr(),
      function_id,
      symbol_table);
  }

  // Rewrite all call sites: pass the address of the receiving variable
  // as the hidden result argument.
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    goto_programt &body = gf_entry.second.body;

    for(auto i_it = body.instructions.begin(); i_it != body.instructions.end();
        ++i_it)
    {
      if(!i_it->is_function_call())
        continue;

      const exprt &function = i_it->call_function();
      if(function.id() != ID_symbol)
        continue;

      const irep_idt callee_id = to_symbol_expr(function).identifier();
      if(!lowered.count(callee_id))
        continue;

      const symbolt &callee_symbol = ns.lookup(callee_id);
      const code_typet &callee_type = to_code_type(callee_symbol.type);
      const typet &slot_type =
        to_pointer_type(callee_type.parameters().back().type()).base_type();

      exprt result_slot;

      if(i_it->call_lhs().is_not_nil())
      {
        result_slot = i_it->call_lhs();
        i_it->call_lhs().make_nil();
      }
      else
      {
        // ignored result: materialize a slot and destroy it afterwards
        symbolt &slot_symbol = get_fresh_aux_symbol(
          slot_type,
          id2string(gf_entry.first),
          "ignored_result",
          i_it->source_location(),
          callee_symbol.mode,
          symbol_table);
        slot_symbol.is_lvalue = true;
        slot_symbol.is_thread_local = true;
        slot_symbol.is_file_local = true;
        slot_symbol.is_state_var = true;

        const symbol_exprt slot = slot_symbol.symbol_expr();
        body.insert_before(
          i_it, goto_programt::make_decl(slot, i_it->source_location()));

        auto after = std::next(i_it);
        if(const auto destructor = find_destructor(slot_type, symbol_table))
        {
          code_function_callt destructor_call{
            *destructor, {address_of_exprt{slot}}};
          after = std::next(body.insert_after(
            i_it,
            goto_programt::make_function_call(
              destructor_call, i_it->source_location())));
        }
        body.insert_after(
          std::prev(after),
          goto_programt::make_dead(slot, i_it->source_location()));

        result_slot = slot;
      }

      i_it->call_arguments().push_back(address_of_exprt{result_slot});
      i_it->call_function().type() = callee_type;
    }
  }

  goto_model.goto_functions.update();
}
