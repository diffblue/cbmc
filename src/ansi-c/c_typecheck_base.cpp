/*******************************************************************\

Module: ANSI-C Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Conversion / Type Checking

#include "c_typecheck_base.h"

#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/std_types.h>
#include <util/symbol_table_base.h>

#include <goto-programs/name_mangler.h>

#include "ansi_c_declaration.h"
#include "c_storage_spec.h"
#include "expr2c.h"

std::string c_typecheck_baset::to_string(const exprt &expr)
{
  return expr2c(expr, *this);
}

std::string c_typecheck_baset::to_string(const typet &type)
{
  return type2c(type, *this);
}

void c_typecheck_baset::move_symbol(symbolt &symbol, symbolt *&new_symbol)
{
  symbol.mode=mode;
  symbol.module=module;

  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "failed to move symbol '" << symbol.name << "' into symbol table"
            << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_symbol(symbolt &symbol)
{
  bool is_function=symbol.type.id()==ID_code;

  // set a few flags
  symbol.is_lvalue=!symbol.is_type && !symbol.is_macro;

  irep_idt root_name=symbol.base_name;
  irep_idt new_name=symbol.name;

  if(symbol.is_file_local)
  {
    // file-local stuff -- stays as is
    // collisions are resolved during linking
  }
  else if(symbol.is_extern && !is_function)
  {
    // variables marked as "extern" go into the global namespace
    // and have static lifetime
    new_name=root_name;
    symbol.is_static_lifetime=true;

    if(symbol.value.is_not_nil() && !symbol.is_macro)
    {
      // According to the C standard this should be an error, but at least some
      // versions of Visual Studio insist to use this in their C library, and
      // GCC just warns as well.
      warning().source_location = symbol.value.find_source_location();
      warning() << "'extern' symbol '" << new_name
                << "' should not have an initializer" << eom;
    }
  }
  else if(!is_function && symbol.value.id()==ID_code)
  {
    error().source_location=symbol.value.find_source_location();
    error() << "only functions can have a function body" << eom;
    throw 0;
  }

  // set the pretty name
  if(symbol.is_type && symbol.type.id() == ID_struct)
  {
    symbol.pretty_name="struct "+id2string(symbol.base_name);
  }
  else if(symbol.is_type && symbol.type.id() == ID_union)
  {
    symbol.pretty_name="union "+id2string(symbol.base_name);
  }
  else if(symbol.is_type && symbol.type.id() == ID_c_enum)
  {
    symbol.pretty_name="enum "+id2string(symbol.base_name);
  }
  else
  {
    symbol.pretty_name=new_name;
  }

  if(!symbol.is_type && !symbol.is_extern && symbol.type.id() == ID_empty)
  {
    error().source_location = symbol.location;
    error() << "void-typed symbol not permitted" << eom;
    throw 0;
  }

  // see if we have it already
  symbol_table_baset::symbolst::const_iterator old_it =
    symbol_table.symbols.find(symbol.name);

  if(old_it==symbol_table.symbols.end())
  {
    // just put into symbol_table
    symbolt *new_symbol;
    move_symbol(symbol, new_symbol);

    typecheck_new_symbol(*new_symbol);
  }
  else
  {
    if(old_it->second.is_type!=symbol.is_type)
    {
      error().source_location=symbol.location;
      error() << "redeclaration of '" << symbol.display_name()
              << "' as a different kind of symbol" << eom;
      throw 0;
    }

    symbolt &existing_symbol = symbol_table.get_writeable_ref(symbol.name);
    if(symbol.is_type)
      typecheck_redefinition_type(existing_symbol, symbol);
    else
    {
      if(
        (!old_it->second.is_static_lifetime || !symbol.is_static_lifetime) &&
        (symbol.type.id() != ID_code &&
         symbol.type.id() != ID_mathematical_function))
      {
        error().source_location = symbol.location;
        error() << "redeclaration of '" << symbol.display_name()
                << "' with no linkage" << eom;
        throw 0;
      }

      typecheck_redefinition_non_type(existing_symbol, symbol);
    }
  }
}

void c_typecheck_baset::typecheck_new_symbol(symbolt &symbol)
{
  if(symbol.is_parameter)
    adjust_function_parameter(symbol.type);

  // check initializer, if needed

  if(symbol.type.id()==ID_code)
  {
    if(symbol.value.is_not_nil() &&
       !symbol.is_macro)
    {
      typecheck_function_body(symbol);
    }
    else if(
      symbol.is_macro ||
      !to_code_with_contract_type(symbol.type).has_contract())
    {
      // we don't need the identifiers
      for(auto &parameter : to_code_type(symbol.type).parameters())
        parameter.set_identifier(irep_idt());
    }
  }
  else if(!symbol.is_macro)
  {
    // check the initializer
    do_initializer(symbol);
  }
}

void c_typecheck_baset::typecheck_redefinition_type(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  const typet &final_old = old_symbol.type;
  const typet &final_new = new_symbol.type;

  // see if we had something incomplete before
  if(
    (final_old.id() == ID_struct &&
     to_struct_type(final_old).is_incomplete()) ||
    (final_old.id() == ID_union && to_union_type(final_old).is_incomplete()) ||
    (final_old.id() == ID_c_enum && to_c_enum_type(final_old).is_incomplete()))
  {
    // is the new one complete?
    if(
      final_new.id() == final_old.id() &&
      ((final_new.id() == ID_struct &&
        !to_struct_type(final_new).is_incomplete()) ||
       (final_new.id() == ID_union &&
        !to_union_type(final_new).is_incomplete()) ||
       (final_new.id() == ID_c_enum &&
        !to_c_enum_type(final_new).is_incomplete())))
    {
      // overwrite location
      old_symbol.location=new_symbol.location;

      // move body
      old_symbol.type.swap(new_symbol.type);
    }
    else if(new_symbol.type.id()==old_symbol.type.id())
      return; // ignore
    else
    {
      error().source_location=new_symbol.location;
      error() << "conflicting definition of type symbol '"
              << new_symbol.display_name() << '\'' << eom;
      throw 0;
    }
  }
  else
  {
    // see if new one is just a tag
    if(
      (final_new.id() == ID_struct &&
       to_struct_type(final_new).is_incomplete()) ||
      (final_new.id() == ID_union &&
       to_union_type(final_new).is_incomplete()) ||
      (final_new.id() == ID_c_enum &&
       to_c_enum_type(final_new).is_incomplete()))
    {
      if(final_old.id() == final_new.id())
      {
        // just ignore silently
      }
      else
      {
        // arg! new tag type
        error().source_location=new_symbol.location;
        error() << "conflicting definition of tag symbol '"
                << new_symbol.display_name() << '\'' << eom;
        throw 0;
      }
    }
    else if(config.ansi_c.os==configt::ansi_ct::ost::OS_WIN &&
            final_new.id()==ID_c_enum && final_old.id()==ID_c_enum)
    {
      // under Windows, ignore this silently;
      // MSC doesn't think this is a problem, but GCC complains.
    }
    else if(
      config.ansi_c.os == configt::ansi_ct::ost::OS_WIN &&
      final_new.id() == ID_pointer && final_old.id() == ID_pointer &&
      to_pointer_type(final_new).base_type().id() == ID_c_enum &&
      to_pointer_type(final_old).base_type().id() == ID_c_enum)
    {
      // under Windows, ignore this silently;
      // MSC doesn't think this is a problem, but GCC complains.
    }
    else
    {
      // see if it changed
      if(new_symbol.type != old_symbol.type)
      {
        error().source_location=new_symbol.location;
        error() << "type symbol '" << new_symbol.display_name()
                << "' defined twice:\n"
                << "Original: " << to_string(old_symbol.type) << "\n"
                << "     New: " << to_string(new_symbol.type) << eom;
        throw 0;
      }
    }
  }
}

static bool is_instantiation_of_flexible_array(
  const struct_typet &old_type,
  const struct_typet &new_type)
{
  const struct_typet::componentst &old_components = old_type.components();
  const struct_typet::componentst &new_components = new_type.components();

  if(old_components.size() != new_components.size())
    return false;

  if(old_components.empty())
    return false;

  for(std::size_t i = 0; i < old_components.size() - 1; ++i)
  {
    if(old_components[i].type() != new_components[i].type())
      return false;
  }

  if(
    old_components.back().type().id() != ID_array ||
    new_components.back().type().id() != ID_array)
  {
    return false;
  }

  const auto &old_array_type = to_array_type(old_components.back().type());
  const auto &new_array_type = to_array_type(new_components.back().type());

  return old_array_type.element_type() == new_array_type.element_type() &&
         old_array_type.get_bool(ID_C_flexible_array_member) &&
         new_array_type.get_bool(ID_C_flexible_array_member) &&
         (old_array_type.size().is_nil() || old_array_type.size().is_zero());
}

void c_typecheck_baset::typecheck_redefinition_non_type(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  const typet &final_old = old_symbol.type;
  const typet &initial_new = new_symbol.type;

  if(
    final_old.id() == ID_array &&
    to_array_type(final_old).size().is_not_nil() &&
    initial_new.id() == ID_array &&
    to_array_type(initial_new).size().is_nil() &&
    to_array_type(final_old).element_type() ==
      to_array_type(initial_new).element_type())
  {
    // this is ok, just use old type
    new_symbol.type=old_symbol.type;
  }
  else if(
    final_old.id() == ID_array && to_array_type(final_old).size().is_nil() &&
    initial_new.id() == ID_array &&
    to_array_type(initial_new).size().is_not_nil() &&
    to_array_type(final_old).element_type() ==
      to_array_type(initial_new).element_type())
  {
    // update the type to enable the use of sizeof(x) on the
    // right-hand side of a definition of x
    old_symbol.type=new_symbol.type;
  }

  // do initializer, this may change the type
  if(
    new_symbol.type.id() != ID_code &&
    new_symbol.type.id() != ID_mathematical_function && !new_symbol.is_macro)
  {
    do_initializer(new_symbol);
  }

  const typet &final_new = new_symbol.type;

  // K&R stuff?
  if(old_symbol.type.id()==ID_KnR)
  {
    // check the type
    if(final_new.id()==ID_code)
    {
      error().source_location=new_symbol.location;
      error() << "function type not allowed for K&R function parameter"
              << eom;
      throw 0;
    }

    // fix up old symbol -- we now got the type
    old_symbol.type=new_symbol.type;
    return;
  }

  if(final_new.id()==ID_code)
  {
    if(final_old.id()!=ID_code)
    {
      error().source_location=new_symbol.location;
      error() << "function symbol '" << new_symbol.display_name()
              << "' redefined with a different type:\n"
              << "Original: " << to_string(old_symbol.type) << "\n"
              << "     New: " << to_string(new_symbol.type) << eom;
      throw 0;
    }

    code_typet &old_ct=to_code_type(old_symbol.type);
    code_typet &new_ct=to_code_type(new_symbol.type);

    if(
      old_ct.return_type() != new_ct.return_type() &&
      !old_ct.get_bool(ID_C_incomplete) &&
      new_ct.return_type().id() != ID_constructor &&
      new_ct.return_type().id() != ID_destructor)
    {
      if(
        old_ct.return_type().id() == ID_constructor ||
        old_ct.return_type().id() == ID_destructor)
      {
        new_ct = old_ct;
      }
      else
      {
        throw invalid_source_file_exceptiont{
          "function symbol '" + id2string(new_symbol.display_name()) +
            "' redefined with a different type:\n" +
            "Original: " + to_string(old_symbol.type) + "\n" +
            "     New: " + to_string(new_symbol.type),
          new_symbol.location};
      }
    }
    const bool inlined = old_ct.get_inlined() || new_ct.get_inlined();

    if(old_ct.has_ellipsis() && !new_ct.has_ellipsis())
      old_ct=new_ct;
    else if(!old_ct.has_ellipsis() && new_ct.has_ellipsis())
    {
      if(to_code_with_contract_type(new_ct).has_contract())
      {
        error().source_location = new_symbol.location;
        error() << "code contract on incomplete function re-declaration" << eom;
        throw 0;
      }
      new_ct=old_ct;
    }

    if(inlined)
    {
      old_ct.set_inlined(true);
      new_ct.set_inlined(true);
    }

    // do body

    if(new_symbol.value.is_not_nil())
    {
      if(old_symbol.value.is_not_nil())
      {
        // gcc allows re-definition if the first
        // definition is marked as "extern inline"

        if(
          old_ct.get_inlined() &&
          (config.ansi_c.mode == configt::ansi_ct::flavourt::GCC ||
           config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ||
           config.ansi_c.mode == configt::ansi_ct::flavourt::ARM ||
           config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO))
        {
          // overwrite "extern inline" properties
          old_symbol.is_extern=new_symbol.is_extern;
          old_symbol.is_file_local=new_symbol.is_file_local;

          // remove parameter declarations to avoid conflicts
          for(const auto &old_parameter : old_ct.parameters())
          {
            const irep_idt &identifier = old_parameter.get_identifier();

            symbol_table_baset::symbolst::const_iterator p_s_it =
              symbol_table.symbols.find(identifier);
            if(p_s_it!=symbol_table.symbols.end())
              symbol_table.erase(p_s_it);
          }
        }
        else
        {
          error().source_location=new_symbol.location;
          error() << "function body '" << new_symbol.display_name()
                  << "' defined twice" << eom;
          throw 0;
        }
      }
      else if(inlined)
      {
        // preserve "extern inline" properties
        old_symbol.is_extern=new_symbol.is_extern;
        old_symbol.is_file_local=new_symbol.is_file_local;
      }
      else if(new_symbol.is_weak)
      {
        // weak symbols
        old_symbol.is_weak=true;
      }

      if(new_symbol.is_macro)
        old_symbol.is_macro=true;
      else
        typecheck_function_body(new_symbol);

      // overwrite location
      old_symbol.location=new_symbol.location;

      // move body
      old_symbol.value.swap(new_symbol.value);

      // overwrite type (because of parameter names)
      old_symbol.type=new_symbol.type;
    }
    else if(to_code_with_contract_type(new_ct).has_contract())
    {
      // overwrite type to add contract, but keep the old parameter identifiers
      // (if any)
      auto new_parameters_it = new_ct.parameters().begin();
      for(auto &p : old_ct.parameters())
      {
        if(new_parameters_it != new_ct.parameters().end())
        {
          new_parameters_it->set_identifier(p.get_identifier());
          ++new_parameters_it;
        }
      }

      old_symbol.type = new_symbol.type;
    }

    return;
  }

  if(final_old!=final_new)
  {
    if(
      final_old.id() == ID_array && to_array_type(final_old).size().is_nil() &&
      final_new.id() == ID_array &&
      to_array_type(final_new).size().is_not_nil() &&
      to_array_type(final_old).element_type() ==
        to_array_type(final_new).element_type())
    {
      old_symbol.type=new_symbol.type;
    }
    else if(
      final_old.id() == ID_pointer &&
      to_pointer_type(final_old).base_type().id() == ID_code &&
      to_code_type(to_pointer_type(final_old).base_type()).has_ellipsis() &&
      final_new.id() == ID_pointer &&
      to_pointer_type(final_new).base_type().id() == ID_code)
    {
      // to allow
      // int (*f) ();
      // int (*f) (int)=0;
      old_symbol.type=new_symbol.type;
    }
    else if(
      final_old.id() == ID_pointer &&
      to_pointer_type(final_old).base_type().id() == ID_code &&
      final_new.id() == ID_pointer &&
      to_pointer_type(final_new).base_type().id() == ID_code &&
      to_code_type(to_pointer_type(final_new).base_type()).has_ellipsis())
    {
      // to allow
      // int (*f) (int)=0;
      // int (*f) ();
    }
    else if(
      final_old.id() == ID_struct_tag && final_new.id() == ID_struct_tag &&
      is_instantiation_of_flexible_array(
        follow_tag(to_struct_tag_type(final_old)),
        follow_tag(to_struct_tag_type(final_new))))
    {
      old_symbol.type = new_symbol.type;
    }
    else
    {
      error().source_location=new_symbol.location;
      error() << "symbol '" << new_symbol.display_name()
              << "' redefined with a different type:\n"
              << "Original: " << to_string(old_symbol.type) << "\n"
              << "     New: " << to_string(new_symbol.type) << eom;
      throw 0;
    }
  }
  else // finals are equal
  {
  }

  // do value
  if(new_symbol.value.is_not_nil())
  {
    // see if we already have one
    if(old_symbol.value.is_not_nil())
    {
      if(
        new_symbol.is_macro && final_new.id() == ID_c_enum &&
        old_symbol.value.is_constant() && new_symbol.value.is_constant() &&
        old_symbol.value.get(ID_value) == new_symbol.value.get(ID_value))
      {
        // ignore
      }
      else
      {
        warning().source_location = new_symbol.value.find_source_location();
        warning() << "symbol '" << new_symbol.display_name()
                  << "' already has an initial value" << eom;
      }
    }
    else
    {
      old_symbol.value=new_symbol.value;
      old_symbol.type=new_symbol.type;
      old_symbol.is_macro=new_symbol.is_macro;
    }
  }

  // take care of some flags
  if(old_symbol.is_extern && !new_symbol.is_extern)
    old_symbol.location=new_symbol.location;

  old_symbol.is_extern=old_symbol.is_extern && new_symbol.is_extern;

  // We should likely check is_volatile and
  // is_thread_local for consistency. GCC complains if these
  // mismatch.
}

void c_typecheck_baset::typecheck_function_body(symbolt &symbol)
{
  if(symbol.value.id() != ID_code)
  {
    error().source_location = symbol.location;
    error() << "function '" << symbol.name << "' is initialized with "
            << symbol.value.id() << eom;
    throw 0;
  }

  code_typet &code_type = to_code_type(symbol.type);

  // reset labels
  labels_used.clear();
  labels_defined.clear();

  // A function declaration int foo(); does not specify the parameter list, but
  // a function definition int foo() { ... } does fix the parameter list to be
  // empty.
  if(code_type.parameters().empty() && code_type.has_ellipsis())
    code_type.remove_ellipsis();

  // fix type
  symbol.value.type()=code_type;

  // set return type
  return_type=code_type.return_type();

  // Add the parameter declarations into the symbol table
  add_parameters_to_symbol_table(symbol);

  // typecheck the body code
  typecheck_code(to_code(symbol.value));

  // check the labels
  for(const auto &label : labels_used)
  {
    if(labels_defined.find(label.first) == labels_defined.end())
    {
      error().source_location = label.second;
      error() << "branching label '" << label.first
              << "' is not defined in function" << eom;
      throw 0;
    }
  }
}

void c_typecheck_baset::apply_asm_label(
  const irep_idt &asm_label,
  symbolt &symbol)
{
  const irep_idt orig_name=symbol.name;

  // restrict renaming to functions and global variables;
  // procedure-local ones would require fixing the scope, as we
  // do for parameters below
  if(!asm_label.empty() &&
     !symbol.is_type &&
     (symbol.type.id()==ID_code || symbol.is_static_lifetime))
  {
    symbol.name=asm_label;
    symbol.base_name=asm_label;
  }

  if(symbol.name!=orig_name)
  {
    if(!asm_label_map.insert(
        std::make_pair(orig_name, asm_label)).second)
    {
      if(asm_label_map[orig_name]!=asm_label)
      {
        error().source_location=symbol.location;
        error() << "replacing asm renaming " << asm_label_map[orig_name]
                << " by " << asm_label << eom;
        throw 0;
      }
    }
  }
  else if(asm_label.empty())
  {
    asm_label_mapt::const_iterator entry=
      asm_label_map.find(symbol.name);
    if(entry!=asm_label_map.end())
    {
      symbol.name=entry->second;
      symbol.base_name=entry->second;
    }
  }

  if(symbol.name!=orig_name &&
     symbol.type.id()==ID_code &&
     symbol.value.is_not_nil() && !symbol.is_macro)
  {
    const code_typet &code_type=to_code_type(symbol.type);

    for(const auto &p : code_type.parameters())
    {
      const irep_idt &p_bn = p.get_base_name();
      if(p_bn.empty())
        continue;

      irep_idt p_id=id2string(orig_name)+"::"+id2string(p_bn);
      irep_idt p_new_id=id2string(symbol.name)+"::"+id2string(p_bn);

      if(!asm_label_map.insert(
          std::make_pair(p_id, p_new_id)).second)
      {
        CHECK_RETURN(asm_label_map[p_id] == p_new_id);
      }
    }
  }
}

void c_typecheck_baset::check_history_expr_return_value(
  const exprt &expr,
  std::string &clause_type)
{
  disallow_subexpr_by_id(
    expr, ID_old, CPROVER_PREFIX "old is not allowed in " + clause_type + ".");
  disallow_subexpr_by_id(
    expr,
    ID_loop_entry,
    CPROVER_PREFIX "loop_entry is not allowed in " + clause_type + ".");

  const irep_idt id = CPROVER_PREFIX "return_value";
  auto pred = [&](const exprt &expr) {
    if(!can_cast_expr<symbol_exprt>(expr))
      return false;

    return to_symbol_expr(expr).get_identifier() == id;
  };

  if(!has_subexpr(expr, pred))
    return;

  throw invalid_source_file_exceptiont(
    id2string(id) + " is not allowed in " + id2string(clause_type) + ".",
    expr.source_location());
}

void c_typecheck_baset::check_was_freed(
  const exprt &expr,
  std::string &clause_type)
{
  const irep_idt id = CPROVER_PREFIX "was_freed";

  auto pred = [&](const exprt &expr) {
    if(!can_cast_expr<symbol_exprt>(expr))
      return false;

    return to_symbol_expr(expr).get_identifier() == id;
  };

  if(has_subexpr(expr, pred))
  {
    throw invalid_source_file_exceptiont(
      id2string(id) + " is not allowed in " + clause_type + ".",
      expr.source_location());
  }
}

void c_typecheck_baset::typecheck_declaration(
  ansi_c_declarationt &declaration)
{
  if(declaration.get_is_static_assert())
  {
    codet code(ID_static_assert);
    code.add_source_location() = declaration.source_location();
    code.operands().swap(declaration.operands());
    typecheck_code(code);
  }
  else
  {
    // get storage spec
    c_storage_spect c_storage_spec(declaration.type());

    // first typecheck the type of the declaration
    typecheck_type(declaration.type());

    // mark as 'already typechecked'
    already_typechecked_typet::make_already_typechecked(declaration.type());

    // Now do declarators, if any.
    for(auto &declarator : declaration.declarators())
    {
      c_storage_spect full_spec(declaration.full_type(declarator));
      full_spec|=c_storage_spec;

      declaration.set_is_inline(full_spec.is_inline);
      declaration.set_is_static(full_spec.is_static);
      declaration.set_is_extern(full_spec.is_extern);
      declaration.set_is_thread_local(full_spec.is_thread_local);
      declaration.set_is_register(full_spec.is_register);
      declaration.set_is_typedef(full_spec.is_typedef);
      declaration.set_is_weak(full_spec.is_weak);

      symbolt symbol = declaration.to_symbol(declarator);
      current_symbol=symbol;

      // now check other half of type
      typecheck_type(symbol.type);

      if(!full_spec.alias.empty())
      {
        if(symbol.value.is_not_nil())
        {
          error().source_location=symbol.location;
          error() << "alias attribute cannot be used with a body"
                  << eom;
          throw 0;
        }

        // alias function need not have been declared yet, thus
        // can't lookup
        // also cater for renaming/placement in sections
        const auto &renaming_entry = asm_label_map.find(full_spec.alias);
        if(renaming_entry == asm_label_map.end())
          symbol.value = symbol_exprt::typeless(full_spec.alias);
        else
          symbol.value = symbol_exprt::typeless(renaming_entry->second);
        symbol.is_macro=true;
      }

      if(full_spec.is_used && symbol.is_file_local)
      {
        // GCC __attribute__((__used__)) - do not treat those as file-local, but
        // make sure the name is unique
        symbol.is_file_local = false;

        symbolt symbol_for_renaming = symbol;
        if(!full_spec.asm_label.empty())
          symbol_for_renaming.name = full_spec.asm_label;
        full_spec.asm_label = djb_manglert{}(
          symbol_for_renaming,
          id2string(symbol_for_renaming.location.get_file()));
      }

      if(full_spec.section.empty())
        apply_asm_label(full_spec.asm_label, symbol);
      else
      {
        // section name is not empty, do a bit of parsing
        std::string asm_name = id2string(full_spec.section);

        if(asm_name[0] == '.')
        {
          std::string::size_type primary_section = asm_name.find('.', 1);

          if(primary_section != std::string::npos)
            asm_name.resize(primary_section);
        }

        asm_name += "$$";

        if(!full_spec.asm_label.empty())
          asm_name+=id2string(full_spec.asm_label);
        else
          asm_name+=id2string(symbol.name);

        apply_asm_label(asm_name, symbol);
      }

      irep_idt identifier=symbol.name;
      declarator.set_name(identifier);

      if(
        symbol.type.id() == ID_code &&
        identifier.starts_with(CPROVER_PREFIX "uninterpreted_"))
      {
        const code_typet &function_call_type = to_code_type(symbol.type);
        mathematical_function_typet::domaint domain;
        for(const auto &parameter : function_call_type.parameters())
          domain.push_back(parameter.type());
        symbol.type =
          mathematical_function_typet{domain, function_call_type.return_type()};
      }

      typecheck_symbol(symbol);

      // check the contract, if any
      symbolt &new_symbol = symbol_table.get_writeable_ref(identifier);
      if(
        new_symbol.type.id() == ID_code &&
        to_code_with_contract_type(new_symbol.type).has_contract())
      {
        code_with_contract_typet code_type =
          to_code_with_contract_type(new_symbol.type);

        // ensure parameter declarations are available for type checking to
        // succeed
        binding_exprt::variablest temporary_parameter_symbols;

        const auto &return_type = code_type.return_type();
        if(return_type.id() != ID_empty)
        {
          parameter_map[CPROVER_PREFIX "return_value"] = return_type;
          temporary_parameter_symbols.emplace_back(
            CPROVER_PREFIX "return_value", return_type);
        }

        std::size_t anon_counter = 0;
        for(auto &p : code_type.parameters())
        {
          // may be anonymous
          if(p.get_base_name().empty())
            p.set_base_name("#anon" + std::to_string(anon_counter++));

          // produce identifier
          const irep_idt &base_name = p.get_base_name();
          irep_idt parameter_identifier =
            id2string(identifier) + "::" + id2string(base_name);

          p.set_identifier(parameter_identifier);

          PRECONDITION(
            parameter_map.find(parameter_identifier) == parameter_map.end());
          parameter_map[parameter_identifier] = p.type();
          temporary_parameter_symbols.emplace_back(
            parameter_identifier, p.type());
        }

        for(auto &c_requires : code_type.c_requires())
        {
          typecheck_expr(c_requires);
          implicit_typecast_bool(c_requires);
          std::string clause_type = "preconditions";
          check_history_expr_return_value(c_requires, clause_type);
          check_was_freed(c_requires, clause_type);
          lambda_exprt lambda{temporary_parameter_symbols, c_requires};
          lambda.add_source_location() = c_requires.source_location();
          c_requires.swap(lambda);
        }

        typecheck_spec_assigns(code_type.c_assigns());
        for(auto &assigns : code_type.c_assigns())
        {
          std::string clause_type = "assigns clauses";
          check_history_expr_return_value(assigns, clause_type);
          lambda_exprt lambda{temporary_parameter_symbols, assigns};
          lambda.add_source_location() = assigns.source_location();
          assigns.swap(lambda);
        }

        typecheck_spec_frees(code_type.c_frees());
        for(auto &frees : code_type.c_frees())
        {
          lambda_exprt lambda{temporary_parameter_symbols, frees};
          lambda.add_source_location() = frees.source_location();
          frees.swap(lambda);
        }

        for(auto &ensures : code_type.c_ensures())
        {
          typecheck_expr(ensures);
          implicit_typecast_bool(ensures);
          disallow_subexpr_by_id(
            ensures,
            ID_loop_entry,
            CPROVER_PREFIX "loop_entry is not allowed in postconditions.");
          lambda_exprt lambda{temporary_parameter_symbols, ensures};
          lambda.add_source_location() = ensures.source_location();
          ensures.swap(lambda);
        }

        for(const auto &parameter_sym : temporary_parameter_symbols)
          parameter_map.erase(parameter_sym.get_identifier());

        // create a contract symbol
        symbolt contract;
        contract.name = "contract::" + id2string(new_symbol.name);
        contract.base_name = new_symbol.base_name;
        contract.pretty_name = new_symbol.pretty_name;
        contract.is_property = true;
        contract.type = code_type;
        contract.mode = new_symbol.mode;
        contract.module = module;
        contract.location = new_symbol.location;

        auto entry = symbol_table.insert(std::move(contract));
        if(!entry.second)
        {
          error().source_location = new_symbol.location;
          error() << "contract '" << new_symbol.display_name()
                  << "' already set at " << entry.first.location.as_string()
                  << eom;
          throw 0;
        }

        // Remove the contract from the original symbol as we have created a
        // dedicated contract symbol.
        new_symbol.type.remove(ID_C_spec_assigns);
        new_symbol.type.remove(ID_C_spec_frees);
        new_symbol.type.remove(ID_C_spec_ensures);
        new_symbol.type.remove(ID_C_spec_requires);
      }
    }
  }
}

void c_typecheck_baset::add_parameters_to_symbol_table(symbolt &symbol)
{
  PRECONDITION(can_cast_type<code_typet>(symbol.type));

  code_typet &code_type = to_code_type(symbol.type);

  unsigned anon_counter = 0;

  // Add the parameter declarations into the symbol table.
  for(auto &p : code_type.parameters())
  {
    // may be anonymous
    if(p.get_base_name().empty())
    {
      irep_idt base_name = "#anon" + std::to_string(anon_counter++);
      p.set_base_name(base_name);
    }

    // produce identifier
    irep_idt base_name = p.get_base_name();
    irep_idt identifier = id2string(symbol.name) + "::" + id2string(base_name);

    p.set_identifier(identifier);

    parameter_symbolt p_symbol;

    p_symbol.type = p.type();
    p_symbol.name = identifier;
    p_symbol.base_name = base_name;
    p_symbol.location = p.source_location();

    symbolt *new_p_symbol;
    move_symbol(p_symbol, new_p_symbol);
  }
}
