/// \file
/// Provide bodies for standard library functions that are declared
/// in headers but defined in libstdc++.so / libc++.so.

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "cpp_typecheck.h"

/// Synthesize a body for _List_node_base::_M_hook.
/// Inserts `this` before `__position` in a doubly-linked list.
static code_blockt
make_list_hook_body(const symbolt &symbol, const namespacet &ns)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  const symbol_exprt this_expr(params[0].get_identifier(), params[0].type());
  const symbol_exprt pos_expr(params[1].get_identifier(), params[1].type());

  const typet &base_type = to_pointer_type(params[0].type()).base_type();
  const struct_typet &struct_type =
    (base_type.id() == ID_struct_tag)
      ? ns.follow_tag(to_struct_tag_type(base_type))
      : to_struct_type(base_type);

  irep_idt next_name, prev_name;
  for(const auto &comp : struct_type.components())
  {
    const std::string bn = id2string(comp.get_base_name());
    if(bn == "_M_next")
      next_name = comp.get_name();
    else if(bn == "_M_prev")
      prev_name = comp.get_name();
  }

  if(next_name.empty() || prev_name.empty())
    return code_blockt();

  const typet ptr_type = params[0].type();
  auto deref_this = dereference_exprt(this_expr);
  auto deref_pos = dereference_exprt(pos_expr);
  auto this_next = member_exprt(deref_this, next_name, ptr_type);
  auto this_prev = member_exprt(deref_this, prev_name, ptr_type);
  auto pos_prev = member_exprt(deref_pos, prev_name, ptr_type);

  code_blockt block;
  // this->_M_next = __position
  block.add(code_frontend_assignt(this_next, pos_expr));
  // this->_M_prev = __position->_M_prev
  block.add(code_frontend_assignt(this_prev, pos_prev));
  // __position->_M_prev->_M_next = this
  auto prev_deref = dereference_exprt(pos_prev);
  auto prev_next = member_exprt(prev_deref, next_name, ptr_type);
  block.add(code_frontend_assignt(prev_next, this_expr));
  // __position->_M_prev = this
  block.add(code_frontend_assignt(pos_prev, this_expr));

  return block;
}

/// Synthesize a body for _List_node_base::_M_unhook.
/// Removes `this` from a doubly-linked list.
static code_blockt
make_list_unhook_body(const symbolt &symbol, const namespacet &ns)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  const symbol_exprt this_expr(params[0].get_identifier(), params[0].type());

  const typet &base_type = to_pointer_type(params[0].type()).base_type();
  const struct_typet &struct_type =
    (base_type.id() == ID_struct_tag)
      ? ns.follow_tag(to_struct_tag_type(base_type))
      : to_struct_type(base_type);

  irep_idt next_name, prev_name;
  for(const auto &comp : struct_type.components())
  {
    const std::string bn = id2string(comp.get_base_name());
    if(bn == "_M_next")
      next_name = comp.get_name();
    else if(bn == "_M_prev")
      prev_name = comp.get_name();
  }

  if(next_name.empty() || prev_name.empty())
    return code_blockt();

  const typet ptr_type = params[0].type();
  auto deref_this = dereference_exprt(this_expr);
  auto this_next = member_exprt(deref_this, next_name, ptr_type);
  auto this_prev = member_exprt(deref_this, prev_name, ptr_type);

  code_blockt block;
  // this->_M_prev->_M_next = this->_M_next
  auto prev_deref = dereference_exprt(this_prev);
  auto prev_next = member_exprt(prev_deref, next_name, ptr_type);
  block.add(code_frontend_assignt(prev_next, this_next));
  // this->_M_next->_M_prev = this->_M_prev
  auto next_deref = dereference_exprt(this_next);
  auto next_prev = member_exprt(next_deref, prev_name, ptr_type);
  block.add(code_frontend_assignt(next_prev, this_prev));

  return block;
}

/// Ensure parameter symbols exist in the symbol table for a function
/// whose body we are synthesizing. Creates identifiers if needed.
static void
ensure_parameter_symbols(symbolt &fn_symbol, symbol_table_baset &symbol_table)
{
  code_typet &fn_type = to_code_type(fn_symbol.type);
  auto &params = fn_type.parameters();
  for(std::size_t i = 0; i < params.size(); ++i)
  {
    irep_idt id = params[i].get_identifier();
    if(id.empty())
    {
      // Create an identifier based on the function name and parameter index
      id = id2string(fn_symbol.name) + "::" + std::to_string(i);
      params[i].set_identifier(id);
    }
    if(symbol_table.has_symbol(id))
      continue;
    symbolt param_sym{id, params[i].type(), fn_symbol.mode};
    param_sym.base_name = params[i].get_base_name();
    param_sym.location = fn_symbol.location;
    param_sym.is_lvalue = true;
    param_sym.is_parameter = true;
    param_sym.is_file_local = true;
    param_sym.is_thread_local = true;
    param_sym.is_state_var = true;
    symbol_table.add(param_sym);
  }
}

void cpp_typecheckt::provide_stdlib_bodies()
{
  namespacet ns(symbol_table);

  // Fix parameter symbols that are missing is_parameter flag.
  for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
  {
    symbolt &symbol = it.get_writeable_symbol();
    if(symbol.type.id() != ID_code)
      continue;
    const code_typet &fn_type = to_code_type(symbol.type);
    for(const auto &param : fn_type.parameters())
    {
      const irep_idt &pid = param.get_identifier();
      if(pid.empty())
        continue;
      symbolt *psym = symbol_table.get_writeable(pid);
      if(psym != nullptr && !psym->is_parameter)
        psym->is_parameter = true;
    }
  }

  for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
  {
    symbolt &symbol = it.get_writeable_symbol();

    if(symbol.type.id() != ID_code)
      continue;

    const std::string base = id2string(symbol.base_name);
    const std::string name = id2string(symbol.name);

    bool is_deferred =
      deferred_typechecking.find(symbol.name) != deferred_typechecking.end();

    // Skip functions that already have properly type-checked bodies
    if(symbol.value.is_not_nil() && !is_deferred)
      continue;

    if(base == "_M_hook" && name.find("_List_node_base") != std::string::npos)
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_list_hook_body(symbol, ns);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base == "_M_unhook" && name.find("_List_node_base") != std::string::npos)
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_list_unhook_body(symbol, ns);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base == "allocate" && name.find("allocator_traits") != std::string::npos)
    {
      // allocator_traits::allocate(alloc, n) → allocate n * sizeof(T) bytes
      const code_typet &fn_type = to_code_type(symbol.type);
      const auto &ret_type = fn_type.return_type();
      if(ret_type.id() == ID_pointer)
      {
        const auto &params = fn_type.parameters();
        if(params.size() >= 2)
        {
          const symbol_exprt n_expr(
            params[1].get_identifier(), params[1].type());
          const auto &elem_type = to_pointer_type(ret_type).base_type();
          auto elem_size = size_of_expr(elem_type, ns);
          if(elem_size.has_value())
          {
            auto total = mult_exprt(
              typecast_exprt::conditional_cast(n_expr, elem_size->type()),
              *elem_size);
            side_effect_exprt alloc{
              ID_allocate, {total, false_exprt()}, ret_type, symbol.location};
            code_blockt block;
            block.add(code_frontend_returnt(alloc));
            ensure_parameter_symbols(symbol, symbol_table);
            symbol.value = std::move(block);
            symbol.value.type() = symbol.type;
            deferred_typechecking.erase(symbol.name);
          }
        }
      }
    }
    else if(
      base == "deallocate" &&
      name.find("allocator_traits") != std::string::npos)
    {
      // allocator_traits::deallocate — make it a no-op for verification
      code_blockt block;
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = std::move(block);
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
    }
  }
}
