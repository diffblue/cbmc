/// \file
/// Provide bodies for standard library functions that are declared
/// in headers but defined in libstdc++.so / libc++.so.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
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

/// Provide constant values for __gnu_cxx::__numeric_traits_integer<T>
/// static members. The C++ front-end leaves these as symbolic expressions
/// that reference other members, but static_lifetime_init initializes
/// symbols in alphabetical order, which breaks the dependency chain
/// (__digits depends on __is_signed, but 'd' < 'i' alphabetically).
static void fold_numeric_traits_integer(symbol_table_baset &symbol_table)
{
  const std::string prefix = "__gnu_cxx::__numeric_traits_integer<";

  for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
  {
    symbolt &symbol = it.get_writeable_symbol();
    const std::string name = id2string(symbol.name);

    if(name.find(prefix) == std::string::npos)
      continue;

    const std::string base = id2string(symbol.base_name);

    // Get the underlying type from __max/__min (which has the _Value type),
    // or handle __is_signed and __digits specially.
    typet value_type = symbol.type;
    value_type.remove(ID_C_constant);

    if(base == "__is_signed")
    {
      // bool: true if the value type is signed
      // The symbol for __max has the actual _Value type; but we can
      // look up the companion __max symbol to determine signedness.
      // Alternatively, check the __max symbol's type.
      irep_idt max_name =
        id2string(symbol.name).substr(0, name.size() - base.size()) + "__max";
      const symbolt *max_sym = symbol_table.lookup(max_name);
      if(max_sym == nullptr)
        continue;
      typet max_type = max_sym->type;
      max_type.remove(ID_C_constant);
      bool is_signed = max_type.id() == ID_signedbv;
      symbol.value = from_integer(is_signed ? 1 : 0, value_type);
    }
    else if(base == "__digits")
    {
      // int: width - is_signed
      irep_idt max_name =
        id2string(symbol.name).substr(0, name.size() - base.size()) + "__max";
      const symbolt *max_sym = symbol_table.lookup(max_name);
      if(max_sym == nullptr)
        continue;
      typet max_type = max_sym->type;
      max_type.remove(ID_C_constant);
      if(!can_cast_type<bitvector_typet>(max_type))
        continue;
      std::size_t width = to_bitvector_type(max_type).get_width();
      bool is_signed = max_type.id() == ID_signedbv;
      mp_integer digits = mp_integer(width) - (is_signed ? 1 : 0);
      symbol.value = from_integer(digits, value_type);
    }
    else if(base == "__max")
    {
      if(!can_cast_type<bitvector_typet>(value_type))
        continue;
      std::size_t width = to_bitvector_type(value_type).get_width();
      mp_integer max_val;
      if(value_type.id() == ID_signedbv)
        max_val = power(2, width - 1) - 1;
      else
        max_val = power(2, width) - 1;
      symbol.value = from_integer(max_val, value_type);
    }
    else if(base == "__min")
    {
      if(!can_cast_type<bitvector_typet>(value_type))
        continue;
      std::size_t width = to_bitvector_type(value_type).get_width();
      mp_integer min_val;
      if(value_type.id() == ID_signedbv)
        min_val = -power(2, width - 1);
      else
        min_val = 0;
      symbol.value = from_integer(min_val, value_type);
    }
  }
}

/// Create a no-op body for an I/O function that returns a reference
/// to its first parameter (e.g., std::endl returns its ostream& argument,
/// ostream::_M_insert returns *this).
static code_blockt make_return_first_param_body(const symbolt &symbol)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.empty())
    return code_blockt();

  const auto &first_param = params[0];
  symbol_exprt param_expr(first_param.get_identifier(), first_param.type());

  // Cast to the return type if needed (e.g., pointer vs reference).
  exprt ret_expr = typecast_exprt(param_expr, fn_type.return_type());

  code_blockt block;
  block.add(code_frontend_returnt(std::move(ret_expr)));
  return block;
}

void cpp_typecheckt::provide_stdlib_bodies()
{
  namespacet ns(symbol_table);

  // Constant-fold __numeric_traits_integer static members to avoid
  // spurious overflow/shift failures from alphabetical init ordering.
  fold_numeric_traits_integer(symbol_table);

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

  // Fix static variables with initializer_list values — convert
  // empty {} to zero-initialized struct values.
  for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
  {
    symbolt &symbol = it.get_writeable_symbol();
    if(
      symbol.is_static_lifetime && symbol.type.id() != ID_code &&
      symbol.value.id() == ID_initializer_list &&
      symbol.value.operands().empty())
    {
      // Replace {} with zero_initializer
      auto zero = ::zero_initializer(symbol.type, symbol.location, ns);
      if(zero.has_value())
        symbol.value = *zero;
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
    else if(
      base == "endl" && name.find("std::") != std::string::npos &&
      name.find("basic_ostream") != std::string::npos)
    {
      // std::endl — model as identity (return the stream argument)
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_return_first_param_body(symbol);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base == "_M_insert" && name.find("basic_ostream") != std::string::npos)
    {
      // basic_ostream::_M_insert — model as returning *this
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_return_first_param_body(symbol);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base == "base" && name.find("__normal_iterator") != std::string::npos &&
      (symbol.value.is_nil() || is_deferred ||
       has_subexpr(symbol.value, ID_cpp_name) ||
       has_subexpr(symbol.value, irep_idt("cpp-this"))))
    {
      // __normal_iterator::base() — return _M_current member
      const code_typet &fn_type = to_code_type(symbol.type);
      const auto &params = fn_type.parameters();
      if(!params.empty())
      {
        ensure_parameter_symbols(symbol, symbol_table);
        // this->_M_current
        const irep_idt &this_id = params[0].get_identifier();
        if(!this_id.empty())
        {
          const typet &this_type = params[0].type();
          // this is a pointer to the struct
          if(this_type.id() == ID_pointer)
          {
            const typet &struct_type = to_pointer_type(this_type).base_type();
            // Look up _M_current component
            if(struct_type.id() == ID_struct_tag)
            {
              const auto &st = ns.follow_tag(to_struct_tag_type(struct_type));
              for(const auto &comp : st.components())
              {
                if(id2string(comp.get_base_name()) == "_M_current")
                {
                  // return (*this)._M_current
                  symbol_exprt this_expr(this_id, this_type);
                  dereference_exprt deref(this_expr);
                  member_exprt mem(deref, comp.get_name(), comp.type());
                  // base() returns a reference — return address
                  typet ret = fn_type.return_type();
                  exprt result = mem;
                  if(is_reference(ret))
                    result = address_of_exprt(mem);
                  code_blockt block;
                  block.add(code_frontend_returnt(std::move(result)));
                  symbol.value = std::move(block);
                  symbol.value.type() = symbol.type;
                  deferred_typechecking.erase(symbol.name);
                  break;
                }
              }
            }
          }
        }
      }
    }
  }
}
