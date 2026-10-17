/// \file
/// Provide bodies for standard library functions that are declared
/// in headers but defined in libstdc++.so / libc++.so.

/// Author: Michael Tautschnig

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_parser.h"
#include "cpp_sfinae_context.h"
#include "cpp_typecheck.h"
#include "itanium_abi_cpp_zero_initializer.h"

#include <sstream>

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
  // Assume the position pointer and its prev pointer are valid.
  // In a properly constructed list, the sentinel node's pointers
  // are always non-NULL (they point to itself for an empty list).
  auto null_ptr = null_pointer_exprt(to_pointer_type(ptr_type));
  block.add(code_assumet(notequal_exprt(pos_expr, null_ptr)));
  block.add(code_assumet(notequal_exprt(pos_prev, null_ptr)));
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
    else
    {
      // Ensure the identifier is fully qualified with the function name.
      // Template instantiation may leave bare parameter names (e.g.,
      // "__last" instead of "function_name::__last"), which collide
      // across different instantiations.
      const std::string id_str = id2string(id);
      const std::string fn_prefix = id2string(fn_symbol.name) + "::";
      if(id_str.find("::") == std::string::npos)
      {
        id = fn_prefix + id_str;
        params[i].set_identifier(id);
      }
      else if(id_str.substr(0, fn_prefix.size()) != fn_prefix)
      {
        // Parameter has a qualified name from a different function
        // (e.g., from a previous template instantiation). Requalify.
        auto pos = id_str.rfind("::");
        id = fn_prefix + id_str.substr(pos + 2);
        params[i].set_identifier(id);
      }
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
      {
        symbol.value = from_integer(0, value_type);
        continue;
      }
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
      {
        symbol.value = from_integer(0, value_type);
        continue;
      }
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

/// \p new_value as a value of \p type: an array constant of the same
/// length gets \p type itself (its size may be spelt with another integer
/// type), anything else a conversion
static exprt component_value(const exprt &new_value, const typet &type)
{
  if(
    new_value.id() == ID_array && type.id() == ID_array &&
    to_array_type(type).size().is_constant() &&
    numeric_cast<mp_integer>(to_array_type(type).size()) ==
      mp_integer{new_value.operands().size()})
  {
    exprt result = new_value;
    result.type() = type;
    return result;
  }
  return typecast_exprt::conditional_cast(new_value, type);
}

/// Create a no-op body for an I/O function that returns a reference
/// to its first parameter (e.g., std::endl returns its ostream& argument,
/// ostream::_M_insert returns *this).
/// N5008 [locale.general]/8: at program startup the global locale is
/// `std::locale::classic()`, the "C" locale.  libstdc++'s facet accessors
/// (`std::use_facet` via `std::__try_use_facet`) read the facet out of
/// `__loc->_M_impl->_M_facets`, which is initialised inside libstdc++.so and
/// therefore invisible to CBMC -- every facet access dereferences a nondet
/// pointer.  Model the ubiquitous `ctype<char>` facet of the "C" locale:
/// a static classification table with the C99 7.4 "C"-locale character
/// classes (`isdigit` is exactly '0'..'9', `isspace` is the six standard
/// white-space characters, etc.), encoded with the same glibc `_ISbit`
/// bit-assignments that the parsed <ctype.h>/<bits/ctype_base.h> gave to
/// `std::ctype_base::digit` and friends (so table entries and user-code
/// masks agree by construction), and a static `ctype<char>` facet object
/// whose `_M_table` points at it.  `ctype<char>::is(mask, char)` is already
/// an inline header body reading `_M_table[(unsigned char)c] & m`, so with
/// this model it evaluates correctly with no virtual dispatch.
/// Returns a nil expression if the ctype<char> struct is not in the symbol
/// table (translation unit does not use `<locale>`).
static exprt provide_classic_ctype_char_model(
  symbol_table_baset &symbol_table,
  const namespacet &ns)
{
  const irep_idt facet_symbol_name =
    "std::" CPROVER_PREFIX "classic_ctype_char";
  if(const symbolt *existing = symbol_table.lookup(facet_symbol_name))
    return existing->symbol_expr();

  const symbolt *ctype_char = symbol_table.lookup("std::tag-ctype<char>");
  if(
    ctype_char == nullptr || ctype_char->type.id() != ID_struct ||
    to_struct_type(ctype_char->type).is_incomplete())
  {
    return nil_exprt{};
  }

  // glibc _ISbit(bit): (bit) < 8 ? ((1 << (bit)) << 8) : ((1 << (bit)) >> 8)
  auto isbit = [](int bit) -> unsigned
  { return bit < 8 ? (1u << bit) << 8 : (1u << bit) >> 8; };
  const unsigned m_upper = isbit(0), m_lower = isbit(1), m_alpha = isbit(2),
                 m_digit = isbit(3), m_xdigit = isbit(4), m_space = isbit(5),
                 m_print = isbit(6), m_graph = isbit(7), m_blank = isbit(8),
                 m_cntrl = isbit(9), m_punct = isbit(10), m_alnum = isbit(11);

  // C99 7.4 "C" locale classification for the 256 unsigned-char values;
  // bytes 128..255 are in no class in the "C" locale.
  const typet mask_type = unsignedbv_typet{16}; // ctype_base::mask
  const std::size_t table_size = 256;
  array_typet table_type{mask_type, from_integer(table_size, size_type())};
  exprt::operandst entries;
  entries.reserve(table_size);
  for(unsigned c = 0; c < table_size; ++c)
  {
    unsigned m = 0;
    const bool upper = c >= 'A' && c <= 'Z';
    const bool lower = c >= 'a' && c <= 'z';
    const bool digit = c >= '0' && c <= '9';
    const bool alpha = upper || lower;
    const bool space =
      c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r';
    const bool print = c >= 0x20 && c <= 0x7e;
    const bool graph = c >= 0x21 && c <= 0x7e;
    const bool cntrl = c <= 0x1f || c == 0x7f;
    const bool xdigit =
      digit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
    const bool alnum = alpha || digit;
    const bool punct = graph && !alnum;
    const bool blank = c == ' ' || c == '\t';
    if(upper)
      m |= m_upper;
    if(lower)
      m |= m_lower;
    if(alpha)
      m |= m_alpha;
    if(digit)
      m |= m_digit;
    if(xdigit)
      m |= m_xdigit;
    if(space)
      m |= m_space;
    if(print)
      m |= m_print;
    if(graph)
      m |= m_graph;
    if(blank)
      m |= m_blank;
    if(cntrl)
      m |= m_cntrl;
    if(punct)
      m |= m_punct;
    if(alnum)
      m |= m_alnum;
    entries.push_back(from_integer(m, mask_type));
  }
  array_exprt table_value{std::move(entries), table_type};

  symbolt table_symbol{
    "std::" CPROVER_PREFIX "classic_ctype_table", table_type, ID_cpp};
  table_symbol.base_name = CPROVER_PREFIX "classic_ctype_table";
  table_symbol.pretty_name = table_symbol.base_name;
  table_symbol.value = std::move(table_value);
  table_symbol.is_static_lifetime = true;
  table_symbol.is_lvalue = true;
  table_symbol.type.set(ID_C_constant, true);
  symbolt *table_ptr = nullptr;
  symbol_table.move(table_symbol, table_ptr);

  // The facet object: zero-initialised ctype<char> with _M_table pointing
  // at the classification table and the widen/narrow caches filled (below);
  // ctype<char>::is, widen and narrow read only those, and no virtual
  // dispatch happens on this object.
  const struct_tag_typet facet_type{ctype_char->name};
  auto facet_zero =
    itanium_abi_cpp_zero_initializer(facet_type, ctype_char->location, ns);
  if(!facet_zero.has_value())
    return nil_exprt{};

  const address_of_exprt table_address{
    index_exprt{table_ptr->symbol_expr(), from_integer(0, c_index_type())}};

  // Set the component named \p name (wherever it sits, including inside a
  // base class component) to \p new_value.
  std::function<bool(
    exprt &, const typet &, const std::string &, const exprt &)>
    set_component = [&](
                      exprt &value,
                      const typet &type,
                      const std::string &name,
                      const exprt &new_value) -> bool
  {
    const typet &followed =
      type.id() == ID_struct_tag
        ? static_cast<const typet &>(ns.follow_tag(to_struct_tag_type(type)))
        : type;
    if(followed.id() != ID_struct || value.id() != ID_struct)
      return false;
    const auto &components = to_struct_type(followed).components();
    // zero_initializer emits one operand per NON-static DATA member; walk
    // components with the same skip rule (see expr_initializer.cpp) to
    // keep the operand index aligned.
    std::size_t op_index = 0;
    for(const auto &component : components)
    {
      if(
        component.type().id() == ID_code || component.get_bool(ID_is_type) ||
        component.get_bool(ID_is_static))
      {
        continue;
      }
      if(op_index >= value.operands().size())
        return false;
      const std::string cname = id2string(component.get_name());
      const std::string suffix = "::" + name;
      if(
        cname == name ||
        (cname.size() > suffix.size() &&
         cname.compare(cname.size() - suffix.size(), suffix.size(), suffix) ==
           0))
      {
        value.operands()[op_index] =
          component_value(new_value, component.type());
        return true;
      }
      if(set_component(
           value.operands()[op_index], component.type(), name, new_value))
      {
        return true;
      }
      ++op_index;
    }
    return false;
  };
  if(!set_component(*facet_zero, facet_type, "_M_table", table_address))
    return nil_exprt{};

  // N5008 [facet.ctype.char.virtuals]/1, [facet.ctype.virtuals]/11: in the
  // "C" locale do_widen and do_narrow apply the simplest reasonable
  // transformation, the identity on char.  libstdc++'s ctype<char>::widen /
  // narrow read the caches _M_widen / _M_narrow when _M_widen_ok /
  // _M_narrow_ok are set (the library fills them from the virtuals in
  // _M_widen_init, whose body is in libstdc++.so); fill them here, so that
  // no virtual call on the modelled object is needed.  libstdc++ 16's
  // stream insertion reaches ctype<char>::widen (basic_ios::widen).
  {
    const typet char_type = ::char_type();
    exprt::operandst identity;
    for(int c = 0; c < 256; ++c)
      identity.push_back(from_integer(c < 128 ? c : c - 256, char_type));
    const array_typet cache_type{char_type, from_integer(256, size_type())};
    const array_exprt cache{identity, cache_type};
    const exprt one = from_integer(1, char_type);
    // older libstdc++ versions without these members keep the facet as is
    set_component(*facet_zero, facet_type, "_M_widen", cache);
    set_component(*facet_zero, facet_type, "_M_widen_ok", one);
    set_component(*facet_zero, facet_type, "_M_narrow", cache);
    set_component(*facet_zero, facet_type, "_M_narrow_ok", one);
  }

  symbolt facet_symbol{facet_symbol_name, facet_type, ID_cpp};
  facet_symbol.base_name = CPROVER_PREFIX "classic_ctype_char";
  facet_symbol.pretty_name = facet_symbol.base_name;
  facet_symbol.value = std::move(*facet_zero);
  facet_symbol.is_static_lifetime = true;
  facet_symbol.is_lvalue = true;
  symbolt *facet_ptr = nullptr;
  symbol_table.move(facet_symbol, facet_ptr);
  return facet_ptr->symbol_expr();
}

/// Set the component of \p value (of type \p type) whose name is or ends in
/// `::\<name\>', looking into base class components too.  \return whether
/// such a component was found.
static bool set_struct_component(
  exprt &value,
  const typet &type,
  const std::string &name,
  const exprt &new_value,
  const namespacet &ns)
{
  const typet &followed =
    type.id() == ID_struct_tag
      ? static_cast<const typet &>(ns.follow_tag(to_struct_tag_type(type)))
      : type;
  if(followed.id() != ID_struct || value.id() != ID_struct)
    return false;
  std::size_t op_index = 0;
  for(const auto &component : to_struct_type(followed).components())
  {
    if(
      component.type().id() == ID_code || component.get_bool(ID_is_type) ||
      component.get_bool(ID_is_static))
    {
      continue;
    }
    if(op_index >= value.operands().size())
      return false;
    const std::string cname = id2string(component.get_name());
    const std::string suffix = "::" + name;
    if(
      cname == name ||
      (cname.size() > suffix.size() &&
       cname.compare(cname.size() - suffix.size(), suffix.size(), suffix) == 0))
    {
      value.operands()[op_index] = component_value(new_value, component.type());
      return true;
    }
    if(set_struct_component(
         value.operands()[op_index], component.type(), name, new_value, ns))
    {
      return true;
    }
    ++op_index;
  }
  return false;
}

/// A static array of \p element_type holding \p text and a terminating
/// zero; \return the address of its first element
static exprt static_character_array(
  symbol_table_baset &symbol_table,
  const std::string &name,
  const typet &element_type,
  const std::string &text)
{
  const irep_idt symbol_name = "std::" CPROVER_PREFIX + name;
  const symbolt *existing = symbol_table.lookup(symbol_name);
  if(existing == nullptr)
  {
    exprt::operandst elements;
    for(char c : text)
      elements.push_back(from_integer(c, element_type));
    elements.push_back(from_integer(0, element_type));
    const array_typet array_type{
      element_type, from_integer(elements.size(), size_type())};
    symbolt array_symbol{symbol_name, array_type, ID_cpp};
    array_symbol.base_name = CPROVER_PREFIX + name;
    array_symbol.pretty_name = array_symbol.base_name;
    array_symbol.value = array_exprt{std::move(elements), array_type};
    array_symbol.is_static_lifetime = true;
    array_symbol.is_lvalue = true;
    symbolt *inserted = nullptr;
    symbol_table.move(array_symbol, inserted);
    existing = inserted;
  }
  return address_of_exprt{
    index_exprt{existing->symbol_expr(), from_integer(0, c_index_type())}};
}

/// N5008 [locale.general]/8: the global locale at program startup is the
/// "C" locale, whose facets libstdc++.so creates (invisible to CBMC).
/// [facet.numpunct.virtuals]/1-6: in it numpunct<C> has the decimal point
/// '.', the thousands separator ',', no grouping, and the names "true" and
/// "false".  libstdc++ reads them through its __numpunct_cache<C>, filled
/// from the facet by __use_cache<__numpunct_cache<C>>; model that cache as
/// a static object holding the "C"-locale values, with libstdc++'s digit
/// atoms (__num_base::_S_atoms_out / _S_atoms_in, the characters of
/// [facet.num.put.virtuals] stage 1 in the "C" locale).
/// \return the cache object, or nil if \p cache_tag is not complete
static exprt classic_numpunct_cache(
  symbol_table_baset &symbol_table,
  const namespacet &ns,
  const irep_idt &cache_tag)
{
  const irep_idt name = id2string(cache_tag) + "::" CPROVER_PREFIX "classic";
  if(const symbolt *existing = symbol_table.lookup(name))
    return existing->symbol_expr();
  const symbolt *cache_class = symbol_table.lookup(cache_tag);
  if(
    cache_class == nullptr || cache_class->type.id() != ID_struct ||
    to_struct_type(cache_class->type).is_incomplete())
  {
    return nil_exprt{};
  }
  const struct_tag_typet cache_type{cache_tag};
  auto value =
    itanium_abi_cpp_zero_initializer(cache_type, cache_class->location, ns);
  if(!value.has_value())
    return nil_exprt{};
  // the character type: that of _M_decimal_point
  typet char_type;
  for(const auto &c : to_struct_type(cache_class->type).components())
  {
    if(c.get_base_name() == "_M_decimal_point")
      char_type = c.type();
  }
  if(char_type.is_nil() || char_type.id().empty())
    return nil_exprt{};
  const std::string suffix =
    char_type.get(ID_C_c_type) == ID_char ? "char" : "wchar_t";
  const auto string_of = [&](const std::string &tag, const std::string &text)
  {
    return static_character_array(
      symbol_table, "classic_" + tag + "_" + suffix, char_type, text);
  };
  bool ok = true;
  const auto set = [&](const char *component, const exprt &v)
  { ok = set_struct_component(*value, cache_type, component, v, ns) && ok; };
  set(
    "_M_grouping",
    static_character_array(
      symbol_table, "classic_grouping", ::char_type(), ""));
  set("_M_grouping_size", from_integer(0, size_type()));
  set("_M_use_grouping", false_exprt{});
  set("_M_truename", string_of("truename", "true"));
  set("_M_truename_size", from_integer(4, size_type()));
  set("_M_falsename", string_of("falsename", "false"));
  set("_M_falsename_size", from_integer(5, size_type()));
  set("_M_decimal_point", from_integer('.', char_type));
  set("_M_thousands_sep", from_integer(',', char_type));
  const auto atoms = [&](const std::string &text)
  {
    exprt::operandst elements;
    for(char c : text)
      elements.push_back(from_integer(c, char_type));
    const array_typet type{char_type, from_integer(text.size(), size_type())};
    return array_exprt{std::move(elements), type};
  };
  set("_M_atoms_out", atoms("-+xX0123456789abcdef0123456789ABCDEF"));
  set("_M_atoms_in", atoms("-+xX0123456789abcdefABCDEF"));
  if(!ok)
    return nil_exprt{};
  symbolt cache_symbol{name, cache_type, ID_cpp};
  cache_symbol.base_name = CPROVER_PREFIX "classic";
  cache_symbol.pretty_name = cache_symbol.base_name;
  cache_symbol.value = std::move(*value);
  cache_symbol.is_static_lifetime = true;
  cache_symbol.is_lvalue = true;
  symbolt *inserted = nullptr;
  symbol_table.move(cache_symbol, inserted);
  return inserted->symbol_expr();
}

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

/// Synthesize a body for std::_Rb_tree_insert_and_rebalance.
///
/// libstdc++ defines this (and the increment/decrement helpers below) in its
/// compiled library (src/c++11/tree.cc); the headers only declare them, so
/// CBMC sees no body.  For functional verification of std::set / std::map
/// (find / count / size / iteration) only the binary-search-tree structure
/// and the header bookkeeping (root = _M_parent, leftmost = _M_left,
/// rightmost = _M_right of the header node) matter.  The red-black colouring
/// and rotations only rebalance the tree; they do not change the ordered
/// container semantics that find/count rely on ([associative.reqmts]).  So
/// model insertion as the plain BST link plus header maintenance that the
/// real routine performs before it rebalances, and omit the rotations.
static code_blockt
make_rb_insert_and_rebalance_body(const symbolt &symbol, const namespacet &ns)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.size() != 4)
    return code_blockt();

  const symbol_exprt insert_left(params[0].get_identifier(), params[0].type());
  const symbol_exprt x_expr(params[1].get_identifier(), params[1].type());
  const symbol_exprt p_expr(params[2].get_identifier(), params[2].type());
  const symbol_exprt header_ref(params[3].get_identifier(), params[3].type());

  const typet ptr_type = params[1].type(); // _Rb_tree_node_base*
  if(ptr_type.id() != ID_pointer)
    return code_blockt();
  const typet &base_type = to_pointer_type(ptr_type).base_type();
  const struct_typet &st = (base_type.id() == ID_struct_tag)
                             ? ns.follow_tag(to_struct_tag_type(base_type))
                             : to_struct_type(base_type);

  irep_idt color_name, parent_name, left_name, right_name;
  typet color_type(ID_nil);
  for(const auto &comp : st.components())
  {
    const std::string bn = id2string(comp.get_base_name());
    if(bn == "_M_color")
    {
      color_name = comp.get_name();
      color_type = comp.type();
    }
    else if(bn == "_M_parent")
      parent_name = comp.get_name();
    else if(bn == "_M_left")
      left_name = comp.get_name();
    else if(bn == "_M_right")
      right_name = comp.get_name();
  }
  if(parent_name.empty() || left_name.empty() || right_name.empty())
    return code_blockt();

  // `&__header`: a reference parameter holds the address of the header node;
  // its pointer value is exactly that address.
  const exprt header_ptr =
    typecast_exprt::conditional_cast(header_ref, ptr_type);
  const auto null_ptr = null_pointer_exprt(to_pointer_type(ptr_type));

  const auto x_deref = dereference_exprt(x_expr);
  const auto p_deref = dereference_exprt(p_expr);
  const auto header_deref = dereference_exprt(header_ptr);

  auto mem = [&](const exprt &obj, const irep_idt &cn)
  { return member_exprt(obj, cn, ptr_type); };

  code_blockt block;
  block.add(code_assumet(notequal_exprt(x_expr, null_ptr)));
  block.add(code_assumet(notequal_exprt(p_expr, null_ptr)));

  // __x->_M_parent = __p;  __x->_M_left = 0;  __x->_M_right = 0;
  // __x->_M_parent = __p;  __x->_M_left = 0;  __x->_M_right = 0;
  block.add(code_frontend_assignt(mem(x_deref, parent_name), p_expr));
  block.add(code_frontend_assignt(mem(x_deref, left_name), null_ptr));
  block.add(code_frontend_assignt(mem(x_deref, right_name), null_ptr));
  // Colour the node black.  The real routine inserts the node red and then
  // rebalances; we omit the rebalancing, and the precise colours do not
  // matter for find/count/size.  But _Rb_tree_decrement's header test relies
  // on the header being the only red node whose grandparent is itself, so
  // every ordinary node (in particular the root) must be non-red.  Black is a
  // valid choice that keeps that test sound.
  if(!color_name.empty() && color_type.is_not_nil())
  {
    typet underlying = color_type;
    if(color_type.id() == ID_c_enum_tag)
      underlying = to_c_enum_type(ns.follow_tag(to_c_enum_tag_type(color_type)))
                     .underlying_type();
    else if(color_type.id() == ID_c_enum)
      underlying = to_c_enum_type(color_type).underlying_type();
    if(underlying.id() == ID_signedbv || underlying.id() == ID_unsignedbv)
      block.add(code_frontend_assignt(
        member_exprt(x_deref, color_name, color_type),
        typecast_exprt(from_integer(1, underlying), color_type))); // _S_black
  }

  // if (__insert_left) {
  //   __p->_M_left = __x;
  //   if (__p == &__header)
  //   { __header._M_parent = __x; __header._M_right = __x; }
  //   else if (__p == __header._M_left) __header._M_left = __x;
  // } else {
  //   __p->_M_right = __x;
  //   if (__p == __header._M_right) __header._M_right = __x;
  // }
  code_blockt left_branch;
  left_branch.add(code_frontend_assignt(mem(p_deref, left_name), x_expr));
  {
    code_blockt empty_tree;
    empty_tree.add(
      code_frontend_assignt(mem(header_deref, parent_name), x_expr));
    empty_tree.add(
      code_frontend_assignt(mem(header_deref, right_name), x_expr));
    code_blockt update_leftmost;
    update_leftmost.add(
      code_frontend_assignt(mem(header_deref, left_name), x_expr));
    left_branch.add(code_ifthenelset(
      equal_exprt(p_expr, header_ptr),
      std::move(empty_tree),
      code_ifthenelset(
        equal_exprt(p_expr, mem(header_deref, left_name)),
        std::move(update_leftmost))));
  }

  code_blockt right_branch;
  right_branch.add(code_frontend_assignt(mem(p_deref, right_name), x_expr));
  {
    code_blockt update_rightmost;
    update_rightmost.add(
      code_frontend_assignt(mem(header_deref, right_name), x_expr));
    right_branch.add(code_ifthenelset(
      equal_exprt(p_expr, mem(header_deref, right_name)),
      std::move(update_rightmost)));
  }

  block.add(code_ifthenelset(
    typecast_exprt::conditional_cast(insert_left, bool_typet()),
    std::move(left_branch),
    std::move(right_branch)));

  return block;
}

/// Synthesize a body for std::_Rb_tree_increment: the in-order successor over
/// the binary-search-tree structure maintained by the insert model above.
/// Used by std::set / std::map forward iteration.  This direction is
/// colour-independent (unlike _Rb_tree_decrement, whose header special case
/// inspects the node colour), so it is sound under the colour-free insert
/// model.
static code_blockt make_rb_increment_body(
  const symbolt &symbol,
  const namespacet &ns,
  symbol_table_baset &symbol_table)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.size() != 1)
    return code_blockt();
  const typet ptr_type = params[0].type();
  if(ptr_type.id() != ID_pointer)
    return code_blockt();
  const symbol_exprt x_expr(params[0].get_identifier(), ptr_type);
  const typet &base_type = to_pointer_type(ptr_type).base_type();
  const struct_typet &st = (base_type.id() == ID_struct_tag)
                             ? ns.follow_tag(to_struct_tag_type(base_type))
                             : to_struct_type(base_type);

  irep_idt parent_name, left_name, right_name;
  for(const auto &comp : st.components())
  {
    const std::string bn = id2string(comp.get_base_name());
    if(bn == "_M_parent")
      parent_name = comp.get_name();
    else if(bn == "_M_left")
      left_name = comp.get_name();
    else if(bn == "_M_right")
      right_name = comp.get_name();
  }
  if(parent_name.empty() || left_name.empty() || right_name.empty())
    return code_blockt();

  // A fresh local for the second cursor.
  const irep_idt y_id = id2string(symbol.name) + "::__cbmc_y";
  if(symbol_table.symbols.find(y_id) == symbol_table.symbols.end())
  {
    symbolt y_sym;
    y_sym.name = y_id;
    y_sym.base_name = "__cbmc_y";
    y_sym.type = ptr_type;
    y_sym.mode = symbol.mode;
    y_sym.is_lvalue = true;
    y_sym.is_thread_local = true;
    y_sym.location = symbol.location;
    symbol_table.insert(std::move(y_sym));
  }
  const symbol_exprt y_expr(y_id, ptr_type);

  auto mem = [&](const exprt &obj, const irep_idt &cn)
  { return member_exprt(obj, cn, ptr_type); };
  auto deref = [&](const exprt &p) { return dereference_exprt(p); };
  const auto null_ptr = null_pointer_exprt(to_pointer_type(ptr_type));

  code_blockt block;
  block.add(code_frontend_declt(y_expr));

  // if (x->_M_right != 0) { x = x->_M_right;
  //                         while (x->_M_left != 0) x = x->_M_left; }
  code_blockt then_b;
  then_b.add(code_frontend_assignt(x_expr, mem(deref(x_expr), right_name)));
  then_b.add(code_whilet(
    notequal_exprt(mem(deref(x_expr), left_name), null_ptr),
    code_frontend_assignt(x_expr, mem(deref(x_expr), left_name))));

  // else { y = x->_M_parent;
  //        while (x == y->_M_right) { x = y; y = y->_M_parent; }
  //        if (x->_M_right != y) x = y; }
  code_blockt else_b;
  else_b.add(code_frontend_assignt(y_expr, mem(deref(x_expr), parent_name)));
  code_blockt loop_b;
  loop_b.add(code_frontend_assignt(x_expr, y_expr));
  loop_b.add(code_frontend_assignt(y_expr, mem(deref(y_expr), parent_name)));
  else_b.add(code_whilet(
    equal_exprt(x_expr, mem(deref(y_expr), right_name)), std::move(loop_b)));
  else_b.add(code_ifthenelset(
    notequal_exprt(mem(deref(x_expr), right_name), y_expr),
    code_frontend_assignt(x_expr, y_expr)));

  block.add(code_ifthenelset(
    notequal_exprt(mem(deref(x_expr), right_name), null_ptr),
    std::move(then_b),
    std::move(else_b)));
  block.add(code_frontend_returnt(x_expr));
  return block;
}

/// Synthesize a body for std::_Rb_tree_decrement: the in-order predecessor
/// over the BST.  Used by std::set / std::map reverse iteration and `--end()`.
/// Mirrors _Rb_tree_increment but adds the header special case: decrementing
/// the past-the-end (header) iterator yields the rightmost element.  libstdc++
/// detects the header as the node that is red and whose grandparent is itself;
/// the insert model colours every ordinary node black, leaving the header (red
/// from _Rb_tree_header construction) as the only such node.
static code_blockt make_rb_decrement_body(
  const symbolt &symbol,
  const namespacet &ns,
  symbol_table_baset &symbol_table)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.size() != 1)
    return code_blockt();
  const typet ptr_type = params[0].type();
  if(ptr_type.id() != ID_pointer)
    return code_blockt();
  const symbol_exprt x_expr(params[0].get_identifier(), ptr_type);
  const typet &base_type = to_pointer_type(ptr_type).base_type();
  const struct_typet &st = (base_type.id() == ID_struct_tag)
                             ? ns.follow_tag(to_struct_tag_type(base_type))
                             : to_struct_type(base_type);

  irep_idt color_name, parent_name, left_name, right_name;
  typet color_type;
  for(const auto &comp : st.components())
  {
    const std::string bn = id2string(comp.get_base_name());
    if(bn == "_M_color")
    {
      color_name = comp.get_name();
      color_type = comp.type();
    }
    else if(bn == "_M_parent")
      parent_name = comp.get_name();
    else if(bn == "_M_left")
      left_name = comp.get_name();
    else if(bn == "_M_right")
      right_name = comp.get_name();
  }
  if(
    color_name.empty() || parent_name.empty() || left_name.empty() ||
    right_name.empty())
    return code_blockt();

  // _S_red == 0
  typet underlying = color_type;
  if(color_type.id() == ID_c_enum_tag)
    underlying = to_c_enum_type(ns.follow_tag(to_c_enum_tag_type(color_type)))
                   .underlying_type();
  else if(color_type.id() == ID_c_enum)
    underlying = to_c_enum_type(color_type).underlying_type();
  if(underlying.id() != ID_signedbv && underlying.id() != ID_unsignedbv)
    return code_blockt();
  const exprt red_const =
    typecast_exprt(from_integer(0, underlying), color_type);

  const irep_idt y_id = id2string(symbol.name) + "::__cbmc_y";
  if(symbol_table.symbols.find(y_id) == symbol_table.symbols.end())
  {
    symbolt y_sym;
    y_sym.name = y_id;
    y_sym.base_name = "__cbmc_y";
    y_sym.type = ptr_type;
    y_sym.mode = symbol.mode;
    y_sym.is_lvalue = true;
    y_sym.is_thread_local = true;
    y_sym.location = symbol.location;
    symbol_table.insert(std::move(y_sym));
  }
  const symbol_exprt y_expr(y_id, ptr_type);

  auto mem = [&](const exprt &obj, const irep_idt &cn)
  { return member_exprt(obj, cn, ptr_type); };
  auto deref = [&](const exprt &p) { return dereference_exprt(p); };
  const auto null_ptr = null_pointer_exprt(to_pointer_type(ptr_type));

  // header: x->_M_color == _S_red && x->_M_parent->_M_parent == x
  const exprt is_header = and_exprt(
    equal_exprt(member_exprt(deref(x_expr), color_name, color_type), red_const),
    equal_exprt(
      mem(deref(mem(deref(x_expr), parent_name)), parent_name), x_expr));

  // header case: x = x->_M_right;  (rightmost)
  code_blockt header_b;
  header_b.add(code_frontend_assignt(x_expr, mem(deref(x_expr), right_name)));

  // else if (x->_M_left != 0) { y = x->_M_left;
  //   while (y->_M_right != 0) y = y->_M_right; x = y; }
  code_blockt has_left_b;
  has_left_b.add(code_frontend_assignt(y_expr, mem(deref(x_expr), left_name)));
  has_left_b.add(code_whilet(
    notequal_exprt(mem(deref(y_expr), right_name), null_ptr),
    code_frontend_assignt(y_expr, mem(deref(y_expr), right_name))));
  has_left_b.add(code_frontend_assignt(x_expr, y_expr));

  // else { y = x->_M_parent;
  //   while (x == y->_M_left) { x = y; y = y->_M_parent; } x = y; }
  code_blockt up_b;
  up_b.add(code_frontend_assignt(y_expr, mem(deref(x_expr), parent_name)));
  code_blockt up_loop;
  up_loop.add(code_frontend_assignt(x_expr, y_expr));
  up_loop.add(code_frontend_assignt(y_expr, mem(deref(y_expr), parent_name)));
  up_b.add(code_whilet(
    equal_exprt(x_expr, mem(deref(y_expr), left_name)), std::move(up_loop)));
  up_b.add(code_frontend_assignt(x_expr, y_expr));

  code_blockt block;
  block.add(code_frontend_declt(y_expr));
  block.add(code_ifthenelset(
    is_header,
    std::move(header_b),
    code_ifthenelset(
      notequal_exprt(mem(deref(x_expr), left_name), null_ptr),
      std::move(has_left_b),
      std::move(up_b))));
  block.add(code_frontend_returnt(x_expr));
  return block;
}

/// Synthesize a body for std::_Rb_tree_rebalance_for_erase: unlink node __z
/// from the tree rooted at __header and return the node that should actually
/// be deallocated.  Used by std::set / std::map erase (the iterator overload;
/// erase-by-key additionally relies on equal_range, handled elsewhere).
///
/// This is the binary-search-tree erase that the real routine performs before
/// it rebalances: the three structural cases (no left child, no right child,
/// two children -> splice in the in-order successor) plus the header
/// bookkeeping (root = _M_parent, leftmost = _M_left, rightmost = _M_right).
/// The red-black rebalancing (recolouring / rotations) that follows in the
/// library is omitted: it does not change the ordered-container semantics
/// that find / count / iteration depend on ([associative.reqmts]).  The
/// __x_parent tracking the real routine keeps solely for that rebalancing is
/// likewise omitted.
static code_blockt make_rb_rebalance_for_erase_body(
  const symbolt &symbol,
  const namespacet &ns,
  symbol_table_baset &symbol_table)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.size() != 2)
    return code_blockt();

  const symbol_exprt z_expr(params[0].get_identifier(), params[0].type());
  const symbol_exprt header_ref(params[1].get_identifier(), params[1].type());

  const typet ptr_type = params[0].type(); // _Rb_tree_node_base*
  if(ptr_type.id() != ID_pointer)
    return code_blockt();
  const typet &base_type = to_pointer_type(ptr_type).base_type();
  const struct_typet &st = (base_type.id() == ID_struct_tag)
                             ? ns.follow_tag(to_struct_tag_type(base_type))
                             : to_struct_type(base_type);

  irep_idt parent_name, left_name, right_name;
  for(const auto &comp : st.components())
  {
    const std::string bn = id2string(comp.get_base_name());
    if(bn == "_M_parent")
      parent_name = comp.get_name();
    else if(bn == "_M_left")
      left_name = comp.get_name();
    else if(bn == "_M_right")
      right_name = comp.get_name();
  }
  if(parent_name.empty() || left_name.empty() || right_name.empty())
    return code_blockt();

  // Fresh locals: the surviving subtree root __x, the spliced node __y, and a
  // scratch cursor __m for the leftmost/rightmost recomputation.
  auto make_local = [&](const std::string &suffix) -> symbol_exprt
  {
    const irep_idt id = id2string(symbol.name) + "::" + suffix;
    if(symbol_table.symbols.find(id) == symbol_table.symbols.end())
    {
      symbolt s;
      s.name = id;
      s.base_name = suffix;
      s.type = ptr_type;
      s.mode = symbol.mode;
      s.is_lvalue = true;
      s.is_thread_local = true;
      s.location = symbol.location;
      symbol_table.insert(std::move(s));
    }
    return symbol_exprt(id, ptr_type);
  };
  const symbol_exprt x_expr = make_local("__cbmc_x");
  const symbol_exprt y_expr = make_local("__cbmc_y");
  const symbol_exprt m_expr = make_local("__cbmc_m");

  auto mem = [&](const exprt &obj, const irep_idt &cn)
  { return member_exprt(obj, cn, ptr_type); };
  auto deref = [&](const exprt &p) { return dereference_exprt(p); };
  const auto null_ptr = null_pointer_exprt(to_pointer_type(ptr_type));
  // `&__header`: a reference parameter holds the address of the header node.
  const exprt header_ptr =
    typecast_exprt::conditional_cast(header_ref, ptr_type);
  const auto h = [&](const irep_idt &cn) { return mem(deref(header_ptr), cn); };

  code_blockt block;
  block.add(code_frontend_declt(x_expr));
  block.add(code_frontend_declt(y_expr));
  block.add(code_frontend_declt(m_expr));

  // __y = __z;  __x = 0;
  block.add(code_frontend_assignt(y_expr, z_expr));
  block.add(code_frontend_assignt(x_expr, null_ptr));

  // if (__z->_M_left == 0) __x = __z->_M_right;
  // else if (__z->_M_right == 0) __x = __z->_M_left;
  // else { __y = __z->_M_right; while (__y->_M_left != 0) __y = __y->_M_left;
  //        __x = __y->_M_right; }
  code_blockt two_child;
  two_child.add(code_frontend_assignt(y_expr, mem(deref(z_expr), right_name)));
  two_child.add(code_whilet(
    notequal_exprt(mem(deref(y_expr), left_name), null_ptr),
    code_frontend_assignt(y_expr, mem(deref(y_expr), left_name))));
  two_child.add(code_frontend_assignt(x_expr, mem(deref(y_expr), right_name)));
  block.add(code_ifthenelset(
    equal_exprt(mem(deref(z_expr), left_name), null_ptr),
    code_frontend_assignt(x_expr, mem(deref(z_expr), right_name)),
    code_ifthenelset(
      equal_exprt(mem(deref(z_expr), right_name), null_ptr),
      code_frontend_assignt(x_expr, mem(deref(z_expr), left_name)),
      std::move(two_child))));

  // Replace __z's parent's link to __z with `repl` (= __y or __x).
  auto relink_parent = [&](const exprt &repl) -> code_ifthenelset
  {
    return code_ifthenelset(
      equal_exprt(h(parent_name), z_expr),
      code_frontend_assignt(h(parent_name), repl),
      code_ifthenelset(
        equal_exprt(
          mem(deref(mem(deref(z_expr), parent_name)), left_name), z_expr),
        code_frontend_assignt(
          mem(deref(mem(deref(z_expr), parent_name)), left_name), repl),
        code_frontend_assignt(
          mem(deref(mem(deref(z_expr), parent_name)), right_name), repl)));
  };

  // Two-child case: __y is __z's successor, splice it into __z's place.
  code_blockt y_ne_z;
  y_ne_z.add(code_frontend_assignt(
    mem(deref(mem(deref(z_expr), left_name)), parent_name), y_expr));
  y_ne_z.add(code_frontend_assignt(
    mem(deref(y_expr), left_name), mem(deref(z_expr), left_name)));
  // if (__y != __z->_M_right) { ... reattach __y's old position ... }
  code_blockt y_ne_zr;
  y_ne_zr.add(code_ifthenelset(
    notequal_exprt(x_expr, null_ptr),
    code_frontend_assignt(
      mem(deref(x_expr), parent_name), mem(deref(y_expr), parent_name))));
  y_ne_zr.add(code_frontend_assignt(
    mem(deref(mem(deref(y_expr), parent_name)), left_name), x_expr));
  y_ne_zr.add(code_frontend_assignt(
    mem(deref(y_expr), right_name), mem(deref(z_expr), right_name)));
  y_ne_zr.add(code_frontend_assignt(
    mem(deref(mem(deref(z_expr), right_name)), parent_name), y_expr));
  y_ne_z.add(code_ifthenelset(
    notequal_exprt(y_expr, mem(deref(z_expr), right_name)),
    std::move(y_ne_zr)));
  y_ne_z.add(relink_parent(y_expr));
  y_ne_z.add(code_frontend_assignt(
    mem(deref(y_expr), parent_name), mem(deref(z_expr), parent_name)));
  y_ne_z.add(code_frontend_assignt(y_expr, z_expr));

  // 0/1-child case (__y == __z): __x replaces __z; fix leftmost/rightmost.
  code_blockt y_eq_z;
  y_eq_z.add(code_ifthenelset(
    notequal_exprt(x_expr, null_ptr),
    code_frontend_assignt(
      mem(deref(x_expr), parent_name), mem(deref(z_expr), parent_name))));
  y_eq_z.add(relink_parent(x_expr));
  // if (leftmost == __z) leftmost = (__z->_M_right == 0) ? __z->_M_parent
  //                                                      : minimum(__x);
  code_blockt left_min;
  left_min.add(code_frontend_assignt(m_expr, x_expr));
  left_min.add(code_whilet(
    notequal_exprt(mem(deref(m_expr), left_name), null_ptr),
    code_frontend_assignt(m_expr, mem(deref(m_expr), left_name))));
  left_min.add(code_frontend_assignt(h(left_name), m_expr));
  y_eq_z.add(code_ifthenelset(
    equal_exprt(h(left_name), z_expr),
    code_ifthenelset(
      equal_exprt(mem(deref(z_expr), right_name), null_ptr),
      code_frontend_assignt(h(left_name), mem(deref(z_expr), parent_name)),
      std::move(left_min))));
  // if (rightmost == __z) rightmost = (__z->_M_left == 0) ? __z->_M_parent
  //                                                       : maximum(__x);
  code_blockt right_max;
  right_max.add(code_frontend_assignt(m_expr, x_expr));
  right_max.add(code_whilet(
    notequal_exprt(mem(deref(m_expr), right_name), null_ptr),
    code_frontend_assignt(m_expr, mem(deref(m_expr), right_name))));
  right_max.add(code_frontend_assignt(h(right_name), m_expr));
  y_eq_z.add(code_ifthenelset(
    equal_exprt(h(right_name), z_expr),
    code_ifthenelset(
      equal_exprt(mem(deref(z_expr), left_name), null_ptr),
      code_frontend_assignt(h(right_name), mem(deref(z_expr), parent_name)),
      std::move(right_max))));

  block.add(code_ifthenelset(
    notequal_exprt(y_expr, z_expr), std::move(y_ne_z), std::move(y_eq_z)));
  block.add(code_frontend_returnt(y_expr));
  return block;
}

/// Synthesize a body for std::__detail::_Prime_rehash_policy::_M_next_bkt.
///
/// libstdc++ defines this in its compiled library
/// (src/c++11/hashtable_c++0x.cc); the headers only declare it, so CBMC
/// sees no body and havocs the call -- the returned bucket count is
/// nondeterministic garbage, _M_rehash then installs a garbage-sized
/// bucket array, and every subsequent bucket-chain walk diverges.
///
/// The real routine returns the next prime >= __n from a static prime
/// table and records the growth threshold `_M_next_resize =
/// prime * max_load_factor` (a mutable member, hence writable through
/// the const `this`).  Per N5008 [unord.req] the exact bucket count is
/// a performance property, not an observable container-semantics one
/// (general requirements only need consistent bucket indexing and
/// finite chains), so the model returns max(__n, 13) -- 13 is the
/// smallest bucket count the real prime table produces for a first
/// insert -- and sets `_M_next_resize` to the same value (i.e. a
/// max_load_factor of 1.0, its default; a user-set smaller factor only
/// changes WHEN growth happens, not functional behaviour).
static code_blockt
make_prime_next_bkt_body(const symbolt &symbol, const namespacet &ns)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.size() != 2)
    return code_blockt();

  const symbol_exprt this_expr(params[0].get_identifier(), params[0].type());
  const symbol_exprt n_expr(params[1].get_identifier(), params[1].type());

  if(params[0].type().id() != ID_pointer)
    return code_blockt();
  const typet &class_type = to_pointer_type(params[0].type()).base_type();
  if(class_type.id() != ID_struct_tag)
    return code_blockt();
  const struct_typet &st = ns.follow_tag(to_struct_tag_type(class_type));

  irep_idt next_resize_name;
  typet next_resize_type;
  for(const auto &comp : st.components())
  {
    if(id2string(comp.get_base_name()) == "_M_next_resize")
    {
      next_resize_name = comp.get_name();
      next_resize_type = comp.type();
    }
  }
  if(next_resize_name.empty())
    return code_blockt();

  const typet &size_type = fn_type.return_type();
  const exprt thirteen = from_integer(13, size_type);

  // result = __n < 13 ? 13 : __n
  const if_exprt result(
    binary_relation_exprt(n_expr, ID_lt, thirteen), thirteen, n_expr);

  code_blockt body;

  // this->_M_next_resize = result  (mutable member, [dcl.stc])
  member_exprt next_resize(
    dereference_exprt(this_expr), next_resize_name, next_resize_type);
  body.add(code_frontend_assignt(
    std::move(next_resize),
    typecast_exprt::conditional_cast(result, next_resize_type)));

  body.add(code_frontend_returnt(result));

  return body;
}

/// Synthesize a body for
/// std::__detail::_Prime_rehash_policy::_M_need_rehash (also defined in
/// libstdc++'s compiled hashtable_c++0x.cc; see make_prime_next_bkt_body).
///
/// Semantics of the real routine: rehash is needed when the element
/// count after the insertion exceeds the recorded growth threshold; the
/// second pair member is then the new bucket count to install.  The
/// model mirrors that with a max_load_factor of 1.0:
///   if (__n_elt + __n_ins > _M_next_resize)
///     { new = max(2*(__n_elt+__n_ins), 13); _M_next_resize = new;
///       return {true, new}; }
///   return {false, 0};
/// Doubling keeps the amortised-growth shape of the original; any
/// deterministic monotone growth preserves container semantics
/// ([unord.req]).
static code_blockt
make_prime_need_rehash_body(const symbolt &symbol, const namespacet &ns)
{
  const code_typet &fn_type = to_code_type(symbol.type);
  const auto &params = fn_type.parameters();
  if(params.size() != 4)
    return code_blockt();

  const symbol_exprt this_expr(params[0].get_identifier(), params[0].type());
  const symbol_exprt n_elt(params[2].get_identifier(), params[2].type());
  const symbol_exprt n_ins(params[3].get_identifier(), params[3].type());

  if(params[0].type().id() != ID_pointer)
    return code_blockt();
  const typet &class_type = to_pointer_type(params[0].type()).base_type();
  if(class_type.id() != ID_struct_tag)
    return code_blockt();
  const struct_typet &st = ns.follow_tag(to_struct_tag_type(class_type));

  irep_idt next_resize_name;
  typet next_resize_type;
  for(const auto &comp : st.components())
  {
    if(id2string(comp.get_base_name()) == "_M_next_resize")
    {
      next_resize_name = comp.get_name();
      next_resize_type = comp.type();
    }
  }
  if(next_resize_name.empty())
    return code_blockt();

  // the return type is std::pair<bool, std::size_t>
  const typet &ret_type = fn_type.return_type();
  if(ret_type.id() != ID_struct_tag)
    return code_blockt();
  const struct_typet &pair_st = ns.follow_tag(to_struct_tag_type(ret_type));

  // build a pair value: start from zero-initialized, then set
  // first/second by component position
  auto make_pair_value =
    [&](const exprt &first_value, const exprt &second_value) -> exprt
  {
    auto zero = itanium_abi_cpp_zero_initializer(ret_type, symbol.location, ns);
    if(!zero.has_value() || zero->id() != ID_struct)
      return nil_exprt();
    struct_exprt pair_value = to_struct_expr(*zero);
    const auto &comps = pair_st.components();
    for(std::size_t i = 0; i < comps.size() && i < pair_value.operands().size();
        ++i)
    {
      const std::string bn = id2string(comps[i].get_base_name());
      if(bn == "first")
        pair_value.operands()[i] =
          typecast_exprt::conditional_cast(first_value, comps[i].type());
      else if(bn == "second")
        pair_value.operands()[i] =
          typecast_exprt::conditional_cast(second_value, comps[i].type());
    }
    return std::move(pair_value);
  };

  const typet &size_type = n_elt.type();
  const plus_exprt total(
    n_elt, typecast_exprt::conditional_cast(n_ins, size_type));
  member_exprt next_resize(
    dereference_exprt(this_expr), next_resize_name, next_resize_type);

  // growth = 2 * total, floored at 13
  const mult_exprt doubled(from_integer(2, size_type), total);
  const exprt thirteen = from_integer(13, size_type);
  const if_exprt new_count(
    binary_relation_exprt(doubled, ID_lt, thirteen), thirteen, doubled);

  const exprt pair_true = make_pair_value(true_exprt(), new_count);
  const exprt pair_false =
    make_pair_value(false_exprt(), from_integer(0, size_type));
  if(pair_true.is_nil() || pair_false.is_nil())
    return code_blockt();

  // if(total > _M_next_resize) { _M_next_resize = new_count;
  //                              return {true, new_count}; }
  code_blockt then_block;
  then_block.add(code_frontend_assignt(
    next_resize,
    typecast_exprt::conditional_cast(new_count, next_resize_type)));
  then_block.add(code_frontend_returnt(pair_true));

  code_blockt body;
  body.add(code_ifthenelset(
    binary_relation_exprt(total, ID_gt, next_resize), std::move(then_block)));
  body.add(code_frontend_returnt(pair_false));

  return body;
}

/// N5008 [locale.general]/8: the num_put<C, ...> facet of the "C" locale,
/// which libstdc++.so creates: a static object of the facet class \p
/// accessor returns a pointer to, zero-initialized (reference count, as
/// locale::classic() does not count) with the vtable pointer of a complete
/// object of the class, so that put() dispatches to its do_put.
/// \return the object, or nil if the class or its vtable is unavailable
exprt cpp_typecheckt::classic_num_put(const symbolt &accessor)
{
  const typet &ret_type = to_code_type(accessor.type).return_type();
  const typet &facet = to_pointer_type(ret_type).base_type();
  if(facet.id() != ID_struct_tag)
    return nil_exprt{};
  const irep_idt facet_tag = to_struct_tag_type(facet).get_identifier();
  const irep_idt name = id2string(facet_tag) + "::" CPROVER_PREFIX "classic";
  if(const symbolt *existing = symbol_table.lookup(name))
    return existing->symbol_expr();
  const symbolt *facet_class = symbol_table.lookup(facet_tag);
  if(
    facet_class == nullptr || facet_class->type.id() != ID_struct ||
    to_struct_type(facet_class->type).is_incomplete())
  {
    return nil_exprt{};
  }
  const namespacet ns{symbol_table};
  const struct_tag_typet facet_type{facet_tag};
  auto value =
    itanium_abi_cpp_zero_initializer(facet_type, facet_class->location, ns);
  if(!value.has_value())
    return nil_exprt{};
  bool vptr_set = false;
  for(const auto &c : to_struct_type(facet_class->type).components())
  {
    if(!c.get_bool(ID_is_vtptr))
      continue;
    const exprt address = vtable_pointer_value(*facet_class, c);
    if(address.is_nil())
      return nil_exprt{};
    if(!set_struct_component(
         *value, facet_type, id2string(c.get_name()), address, ns))
    {
      return nil_exprt{};
    }
    vptr_set = true;
  }
  if(!vptr_set)
    return nil_exprt{};
  symbolt facet_symbol{name, facet_type, ID_cpp};
  facet_symbol.base_name = CPROVER_PREFIX "classic";
  facet_symbol.pretty_name = facet_symbol.base_name;
  facet_symbol.value = std::move(*value);
  facet_symbol.is_static_lifetime = true;
  facet_symbol.is_lvalue = true;
  symbolt *inserted = nullptr;
  symbol_table.move(facet_symbol, inserted);
  return inserted->symbol_expr();
}

/// Bodies, in C++, of functions that libc++ (LLVM 18) declares in its
/// headers and defines in its compiled library (src/*.cpp there), keyed by
/// the function's name without its parameter list.  The std::bad_alloc
/// members are out of line in libstdc++, too.  Each body is the one
/// libc++ uses, simplified where only concurrent executions could tell the
/// difference.
static const std::map<std::string, std::string> &library_source_models()
{
  static const std::map<std::string, std::string> models = {
    // libc++ src/memory.cpp; the acquire-load shortcut only avoids the
    // decrement when no weak owner is left, with the same outcome
    {"std::__1::__shared_weak_count::__release_weak",
     "{ if(__libcpp_atomic_refcount_decrement(__shared_weak_owners_) == -1)"
     " __on_zero_shared_weak(); }"},
    {"std::__1::__shared_weak_count::lock",
     "{ if(__shared_owners_ == -1) return nullptr;"
     " __libcpp_atomic_refcount_increment(__shared_owners_); return this; }"},
    {"std::__1::__shared_weak_count::__get_deleter", "{ return nullptr; }"},
    {"std::__1::__shared_weak_count::~__shared_weak_count", "{ }"},
    {"std::__1::__shared_count::~__shared_count", "{ }"},
    // libc++ src/hash.cpp: the smallest prime not less than __n (libc++
    // throws overflow_error past the largest size_t prime)
    {"std::__1::__next_prime",
     "{ if(__n <= 2) return 2;"
     " for(size_t __p = __n | 1;; __p += 2) {"
     " bool __prime = true;"
     " for(size_t __d = 3; __d <= __p / __d; __d += 2)"
     " if(__p % __d == 0) { __prime = false; break; }"
     " if(__prime) return __p; } }"},
    // libc++ src/support/runtime/exception_fallback.ipp, N5008
    // [exception]
    // libstdc++ config/os/gnu-linux/ctype_noninline.h: the "C" locale's
    // ctype<char> case mappings ([locale.ctype.virtuals]/7, /9); keyed by
    // the full identifier, for the two overloads each
    {"std::ctype<char>::do_tolower($constthis,char)",
     "{ return __c >= 'A' && __c <= 'Z' ? char(__c - 'A' + 'a') : __c; }"},
    {"std::ctype<char>::do_toupper($constthis,char)",
     "{ return __c >= 'a' && __c <= 'z' ? char(__c - 'a' + 'A') : __c; }"},
    {"std::ctype<char>::do_tolower($constthis,ptr_char,ptr_const_char)",
     "{ for(; __lo < __hi; ++__lo) *__lo = do_tolower(*__lo); return __hi; }"},
    {"std::ctype<char>::do_toupper($constthis,ptr_char,ptr_const_char)",
     "{ for(; __lo < __hi; ++__lo) *__lo = do_toupper(*__lo); return __hi; }"},
    // the MSVC runtime's type_info support (vcruntime_typeinfo.h): cbmc
    // gives each type one type_info object (typecheck_expr_typeid), so
    // their data compare equal iff they are the same object, as N5008
    // [type.info]/2 requires; the order of before() is unspecified
    // ([type.info]/4), the hash equal for equal objects ([type.info]/7)
    {"__std_type_info_compare",
     "{ return _Lhs == _Rhs ? 0 :"
     " ((unsigned long long)_Lhs < (unsigned long long)_Rhs ? -1 : 1); }"},
    {"__std_type_info_hash", "{ return (unsigned long long)_Data; }"},
    {"std::exception::~exception", "{ }"},
    {"std::exception::what", "{ return \"std::exception\"; }"},
    // libc++ src/new.cpp, N5008 [bad.alloc], [new.badlength]
    {"std::bad_alloc::bad_alloc", "{ }"},
    {"std::bad_alloc::~bad_alloc", "{ }"},
    {"std::bad_alloc::what", "{ return \"std::bad_alloc\"; }"},
    {"std::bad_array_new_length::bad_array_new_length", "{ }"},
    {"std::bad_array_new_length::~bad_array_new_length", "{ }"},
    {"std::bad_array_new_length::what", "{ return \"bad_array_new_length\"; }"},
  };
  return models;
}

void cpp_typecheckt::provide_library_source_models()
{
  std::vector<std::pair<irep_idt, const std::string *>> to_define;
  for(const auto &entry : symbol_table.symbols)
  {
    const symbolt &symbol = entry.second;
    // extern "C" functions declared in C++ (the MSVC runtime's
    // __std_type_info_compare) have mode C
    if(
      symbol.type.id() != ID_code || symbol.value.is_not_nil() ||
      symbol.is_type || (symbol.mode != ID_cpp && symbol.mode != ID_C))
    {
      continue;
    }
    const std::string name = id2string(symbol.name);
    auto model = library_source_models().find(name);
    if(model == library_source_models().end())
      model = library_source_models().find(name.substr(0, name.find('(')));
    if(model != library_source_models().end())
      to_define.emplace_back(entry.first, &model->second);
  }

  for(const auto &item : to_define)
  {
    // the body, parsed as that of a function definition
    std::istringstream in{
      "void " CPROVER_PREFIX "library_model() " + *item.second};
    cpp_parsert parser{get_message_handler()};
    parser.set_file(ID_built_in);
    parser.in = &in;
    parser.mode = config.ansi_c.mode;
    if(
      parser.parse() || parser.parse_tree.items.size() != 1 ||
      !parser.parse_tree.items.front().is_declaration())
    {
      continue;
    }
    cpp_declarationt &declaration =
      parser.parse_tree.items.front().get_declaration();
    if(declaration.declarators().size() != 1)
      continue;
    exprt body = declaration.declarators().front().value();

    symbolt &symbol = symbol_table.get_writeable_ref(item.first);
    symbol.value = body;
    try
    {
      sfinae_contextt sfinae_guard{*this};
      // a constructor initializes its bases and members and installs the
      // virtual pointers before its body ([class.base.init]/13, Itanium C++
      // ABI 2.6), as for a constructor defined in the program
      const code_typet &code_type = to_code_type(symbol.type);
      if(
        code_type.return_type().id() == ID_constructor &&
        !code_type.parameters().empty() &&
        code_type.parameters().front().type().id() == ID_pointer)
      {
        const typet &class_tag =
          to_pointer_type(code_type.parameters().front().type()).base_type();
        const symbolt *class_symbol =
          class_tag.id() == ID_struct_tag
            ? symbol_table.lookup(
                to_struct_tag_type(class_tag).get_identifier())
            : nullptr;
        if(class_symbol == nullptr || class_symbol->type.id() != ID_struct)
          continue;
        const struct_typet &class_type = to_struct_type(class_symbol->type);
        irept initializers{ID_member_initializers};
        cpp_save_scopet save_scope{cpp_scopes};
        cpp_scopes.set_scope(class_symbol->name);
        check_member_initializers(
          class_type.bases(),
          class_type.components(),
          initializers,
          class_symbol->name);
        full_member_initialization(class_type, initializers);
        move_member_initializers(initializers, code_type, symbol.value);
      }
      convert_function(symbol);
    }
    catch(...)
    {
      symbol.value.make_nil();
    }
    if(!symbol.value.get_bool("#cpp_converted"))
      symbol.value.make_nil();
  }
}

void cpp_typecheckt::provide_stdlib_bodies()
{
  namespacet ns(symbol_table);

  // Constant-fold __numeric_traits_integer static members to avoid
  // spurious overflow/shift failures from alphabetical init ordering.
  fold_numeric_traits_integer(symbol_table);

  // Fold __safe_multiply::__c to avoid division-by-zero in <ratio>.
  // __c = uintmax_t(1) << (sizeof(intmax_t) * 4) which is 2^32 on
  // 64-bit systems. CBMC's constexpr evaluation may fail to compute
  // this inside template classes on older GCC.
  for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
  {
    symbolt &sym = it.get_writeable_symbol();
    const std::string sname = id2string(sym.name);
    if(
      id2string(sym.base_name) == "__c" &&
      sname.find("__safe_multiply") != std::string::npos)
    {
      sym.value = from_integer(mp_integer(1) << 32, sym.type);
      sym.is_macro = true;
    }
  }

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
      auto zero =
        itanium_abi_cpp_zero_initializer(symbol.type, symbol.location, ns);
      if(zero.has_value())
        symbol.value = *zero;
    }
  }

  // The models below add parameter symbols (ensure_parameter_symbols) while
  // the functions are visited; an insertion may rehash the symbol table's
  // unordered_map and invalidate the iteration (functions get skipped -- the
  // locale default-constructor model went missing that way).  Visit a
  // snapshot of the function names instead.
  std::vector<irep_idt> function_names;
  for(const auto &named_symbol : symbol_table.symbols)
  {
    if(named_symbol.second.type.id() == ID_code)
      function_names.push_back(named_symbol.first);
  }

  for(const irep_idt &function_name : function_names)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(function_name);

    const std::string base = id2string(symbol.base_name);
    const std::string name = id2string(symbol.name);

    bool is_deferred =
      deferred_typechecking.find(symbol.name) != deferred_typechecking.end();

    // Skip functions that already have properly type-checked bodies
    // (except for specific functions we need to override)
    if(symbol.value.is_not_nil() && !is_deferred)
    {
      if(
        (base.find("__try_use_facet") == 0 || base.find("use_facet") == 0) &&
        name.find("<std::tag-ctype<char>>") != std::string::npos &&
        to_code_type(symbol.type).return_type().id() == ID_pointer)
      {
        // Override the header-inline body, which reads the invisible
        // libstdc++-internal __loc->_M_impl->_M_facets table, with a
        // return of the modelled classic-"C" ctype<char> facet
        // ([locale.general]/8: the startup global locale is the "C"
        // locale).  See provide_classic_ctype_char_model.  libstdc++ 13
        // routes use_facet through __try_use_facet; libstdc++ 11's
        // use_facet<_Facet>(const locale&) reads the table itself and
        // returns `const _Facet&' (a pointer here), so it is overridden the
        // same way.
        exprt facet = provide_classic_ctype_char_model(symbol_table, ns);
        // N5008 [locale.ctype.members]: tolower/toupper call the virtual
        // do_tolower/do_toupper; the modelled object needs the vtable
        // pointer of a complete ctype<char> (the virtuals are modelled in
        // library_source_models)
        if(facet.is_not_nil())
        {
          symbolt &fs = symbol_table.get_writeable_ref(
            to_symbol_expr(facet).get_identifier());
          const symbolt *facet_class =
            fs.type.id() == ID_struct_tag
              ? symbol_table.lookup(
                  to_struct_tag_type(fs.type).get_identifier())
              : nullptr;
          if(facet_class != nullptr && facet_class->type.id() == ID_struct)
          {
            for(const auto &c : to_struct_type(facet_class->type).components())
            {
              if(!c.get_bool(ID_is_vtptr))
                continue;
              const exprt address = vtable_pointer_value(*facet_class, c);
              if(address.is_not_nil())
              {
                set_struct_component(
                  fs.value, fs.type, id2string(c.get_name()), address, ns);
              }
            }
          }
        }
        if(facet.is_not_nil())
        {
          const typet &ret_type = to_code_type(symbol.type).return_type();
          ensure_parameter_symbols(symbol, symbol_table);
          code_blockt block;
          block.add(code_frontend_returnt(typecast_exprt::conditional_cast(
            address_of_exprt{facet}, ret_type)));
          symbol.value = std::move(block);
          symbol.value.type() = symbol.type;
          deferred_typechecking.erase(symbol.name);
        }
      }
      else if(
        (base.find("__try_use_facet") == 0 || base.find("use_facet") == 0) &&
        name.find("<std::tag-num_put<") != std::string::npos &&
        to_code_type(symbol.type).return_type().id() == ID_pointer &&
        classic_num_put(symbol).is_not_nil())
      {
        // N5008 [locale.general]/8: the "C" locale has a num_put<C, ...>
        // facet; return such an object (classic_num_put), so that stream
        // insertion of arithmetic values ([ostream.inserters.arithmetic])
        // calls num_put's own do_put
        const typet &ret_type = to_code_type(symbol.type).return_type();
        ensure_parameter_symbols(symbol, symbol_table);
        code_blockt block;
        block.add(code_frontend_returnt{typecast_exprt::conditional_cast(
          address_of_exprt{classic_num_put(symbol)}, ret_type)});
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
      else if(
        base == "operator()" &&
        name.find("__use_cache<std::tag-__numpunct_cache<") !=
          std::string::npos &&
        to_code_type(symbol.type).return_type().id() == ID_pointer)
      {
        // the "C"-locale numpunct data (classic_numpunct_cache)
        const typet &ret_type = to_code_type(symbol.type).return_type();
        const typet &cache_type = to_pointer_type(ret_type).base_type();
        exprt cache = cache_type.id() == ID_struct_tag
                        ? classic_numpunct_cache(
                            symbol_table,
                            ns,
                            to_struct_tag_type(cache_type).get_identifier())
                        : nil_exprt{};
        if(cache.is_not_nil())
        {
          ensure_parameter_symbols(symbol, symbol_table);
          code_blockt block;
          block.add(code_frontend_returnt{typecast_exprt::conditional_cast(
            address_of_exprt{cache}, ret_type)});
          symbol.value = std::move(block);
          symbol.value.type() = symbol.type;
          deferred_typechecking.erase(symbol.name);
        }
      }
      else if(
        base.find("__try_use_facet") == 0 &&
        to_code_type(symbol.type).return_type().id() == ID_pointer)
      {
        // Facet types OTHER than the modelled ctype<char>: the
        // header-inline body reads the libstdc++-internal
        // __loc->_M_impl->_M_facets table, which CBMC does not model
        // (see above), so every stream construction fails its cache
        // lookups (_M_cache_locale caching num_put/num_get,
        // [basic.ios.cons]).  __try_use_facet's contract is to return
        // a null pointer when the requested facet is absent
        // ([locale.general]; use_facet throws bad_cast in that case,
        // has_facet returns false): returning null models a locale
        // that only provides the facets CBMC implements, and any
        // genuine USE of an unmodelled facet still fails visibly at
        // the use site rather than through an unconstrained read.
        const typet &ret_type = to_code_type(symbol.type).return_type();
        ensure_parameter_symbols(symbol, symbol_table);
        code_blockt block;
        block.add(
          code_frontend_returnt{null_pointer_exprt{to_pointer_type(ret_type)}});
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
      else if(
        base.find("has_facet") == 0 &&
        to_code_type(symbol.type).return_type().id() == ID_c_bool &&
        name.find("locale") != std::string::npos)
      {
        // libstdc++ 11's has_facet<_Facet>(const locale&) reads the same
        // internal __loc._M_impl->_M_facets table (libstdc++ 13's goes
        // through __try_use_facet, modelled above).  Answer as that model
        // does: the classic ctype<char> and num_put facets are present,
        // every other facet is absent ([locale.general]/8; _M_cache_locale
        // then caches a null num_get pointer instead of failing on the
        // table read).
        ensure_parameter_symbols(symbol, symbol_table);
        code_blockt block;
        const typet &ret_type = to_code_type(symbol.type).return_type();
        // (also num_put, see classic_num_put: libstdc++ 11's use_facet
        // returns that object, and the stream's cached _M_num_put must not
        // be null -- __check_facet then calls the bodyless
        // __throw_bad_cast)
        const bool present =
          name.find("<std::tag-ctype<char>>") != std::string::npos ||
          name.find("<std::tag-num_put<") != std::string::npos;
        block.add(
          code_frontend_returnt{from_integer(present ? 1 : 0, ret_type)});
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
      else if(base == "_S_nothrow_relocate" || base == "_S_use_relocate")
      {
        // Override: return true so the _S_relocate path is taken
        // (which we model) instead of __uninitialized_move_if_noexcept_a.
        // Clear is_macro so the function is called at runtime using
        // our model body, not evaluated as constexpr (which may
        // produce nondet on older GCC).
        ensure_parameter_symbols(symbol, symbol_table);
        symbol.is_macro = false;
        code_blockt block;
        block.add(code_frontend_returnt(true_exprt()));
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
      else if(
        base == "_M_realloc_insert" && name.find("vector") != std::string::npos)
      {
        // Remove __new_finish=pointer() initialization from the body.
        // Walk the body looking for decl-init pairs where __new_finish
        // is initialized to a zero/NULL value, and remove the init.
        std::function<void(exprt &)> fix = [&](exprt &e)
        {
          // Look for side_effect assign: __new_finish = <null>
          if(
            e.id() == ID_side_effect && e.get(ID_statement) == ID_assign &&
            e.operands().size() == 2 && e.operands()[0].id() == ID_symbol &&
            id2string(to_symbol_expr(e.operands()[0]).get_identifier())
                .find("__new_finish") != std::string::npos &&
            (e.operands()[1].is_zero() || e.operands()[1].is_constant() ||
             e.operands()[1].id() == ID_side_effect))
          {
            // Check if RHS is a zero-valued constructor call
            const auto &rhs = e.operands()[1];
            if(
              rhs.is_zero() ||
              (rhs.id() == ID_constant &&
               (rhs.get(ID_value) == "NULL" || rhs.get(ID_value) == "0")) ||
              (rhs.id() == ID_side_effect &&
               rhs.get(ID_statement) == ID_temporary_object))
            {
              // Replace with: __new_finish = __new_finish (no-op)
              e.operands()[1] = e.operands()[0];
            }
          }
          for(auto &op : e.operands())
            fix(op);
        };
        fix(symbol.value);
      }
      else if(
        base.find("__uninitialized_move_if_noexcept_a") == 0 ||
        base.find("__uninitialized_copy_a") == 0)
      {
        // Override with array_replace model (same as _S_relocate).
        ensure_parameter_symbols(symbol, symbol_table);
        const auto &params = to_code_type(symbol.type).parameters();
        if(params.size() >= 3)
        {
          symbol_exprt first(params[0].get_identifier(), params[0].type());
          symbol_exprt last(params[1].get_identifier(), params[1].type());
          symbol_exprt result(params[2].get_identifier(), params[2].type());
          const auto &ret_type = to_code_type(symbol.type).return_type();

          auto get_ptr = [&](symbol_exprt &sym) -> exprt
          {
            if(sym.type().id() == ID_struct_tag)
            {
              const auto &st = follow_tag(to_struct_tag_type(sym.type()));
              for(const auto &comp : st.components())
              {
                if(
                  id2string(comp.get_name()).find("_M_current") !=
                  std::string::npos)
                  return member_exprt{sym, comp.get_name(), comp.type()};
              }
            }
            return sym;
          };
          exprt first_ptr = get_ptr(first);
          exprt last_ptr = get_ptr(last);
          // the model copies between pointers; other iterators (std::deque's
          // _Deque_iterator, whose position is _M_cur) keep the library's own
          // element-wise body -- an array_replace of the iterator objects
          // violated symex's pointer precondition (`std::deque<bool> e(d)')
          if(
            first_ptr.type().id() == ID_pointer &&
            last_ptr.type().id() == ID_pointer &&
            result.type().id() == ID_pointer && !is_reference(result.type()))
          {
            minus_exprt count{last_ptr, first_ptr};
            count.type() = pointer_diff_type();
            plus_exprt ret_val{result, count};
            ret_val.type() = ret_type;

            code_blockt copy_block;
            copy_block.add(codet{ID_array_replace, {result, first_ptr}});
            copy_block.add(code_frontend_returnt{ret_val});

            code_blockt block;
            block.add(code_ifthenelset{
              notequal_exprt{first_ptr, last_ptr},
              std::move(copy_block),
              code_frontend_returnt{result}});
            symbol.value = std::move(block);
            symbol.value.type() = symbol.type;
          }
        }
      }
      else if(
        base == "__exchange_and_add_single" ||
        base == "__exchange_and_add_dispatch")
      {
        // Override: add assume(__mem != NULL) before the body.
        ensure_parameter_symbols(symbol, symbol_table);
        const auto &params = to_code_type(symbol.type).parameters();
        if(!params.empty())
        {
          symbol_exprt mem(params[0].get_identifier(), params[0].type());
          auto null_ptr = null_pointer_exprt(to_pointer_type(mem.type()));
          // Prepend assumes to existing body:
          // 1. __mem is non-NULL (valid shared_ptr control block)
          // 2. *__mem >= 0 (reference counts are non-negative)
          if(symbol.value.id() == ID_code)
          {
            code_blockt block;
            block.add(code_assumet(notequal_exprt(mem, null_ptr)));
            auto deref = dereference_exprt(mem);
            block.add(code_assumet(binary_relation_exprt(
              deref, ID_ge, from_integer(0, deref.type()))));
            block.add(to_code(symbol.value));
            symbol.value = std::move(block);
          }
        }
      }
      else if(
        name.find("std::_Destroy<") != std::string::npos &&
        name.find("_Destroy_aux") == std::string::npos)
      {
        // Override: std::_Destroy(first, last) — no-op for scalars
        ensure_parameter_symbols(symbol, symbol_table);
        symbol.value = code_blockt();
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }

      continue;
    }

    // Provide model for _S_use_relocate/_S_nothrow_relocate regardless
    // of whether they already have a value.
    if(
      (base == "_S_nothrow_relocate" || base == "_S_use_relocate") &&
      name.find("vector") != std::string::npos)
    {
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.is_macro = false;
      code_blockt block;
      block.add(code_frontend_returnt(true_exprt()));
      symbol.value = std::move(block);
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }

    if(base == "__do_upcast" && name.find("type_info") != std::string::npos)
    {
      // type_info::__do_upcast — RTTI helper, provide empty body
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }

    if(name.find("std::any::any") != std::string::npos && symbol.value.is_nil())
    {
      // std::any constructor — deferred type-checking fails on GCC 12/15
      // due to noexcept specifier with __is_nothrow_new_constructible.
      // Provide empty body (any_cast will return nondet).
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }

    // GCC 16+ system header functions that lack bodies.
    if(
      symbol.value.is_nil() &&
      (name == "__glibcxx_assert_fail" || name == "std::__glibcxx_assert_fail"))
    {
      // libstdc++ assertion handler — provide empty body (assume no
      // assertion failures in the standard library).
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }

    // libc++ (LLVM) defines these in libc++.so (src/ios.cpp,
    // src/locale.cpp), so CBMC sees no body and every stream's state is
    // nondeterministic.  Model them by their specified effects:
    //   ios_base::init(void *sb): N5008 [basic.ios.cons] Table 128 --
    //     rdbuf() == sb, tie() == 0 (basic_ios::init's own part),
    //     rdstate() == goodbit if sb is not null, else badbit,
    //     exceptions() == goodbit, flags() == skipws | dec, width() == 0,
    //     precision() == 6; no callbacks or iword/pword storage
    //     ([ios.base.callback], [ios.base.storage]) yet.  The locale
    //     storage __loc_ is left null, denoting the global "C" locale as in
    //     the libstdc++ model below.
    //   ios_base::~ios_base(): [ios.base.cons]/2 -- the erase_event
    //     callbacks (none registered by these models), then the storage is
    //     released: no observable effect.
    //   locale::locale(), locale(const locale &), ~locale(): the __imp *
    //     __locale_ is null (the global "C" locale, [locale.cons]/2) or the
    //     other's ([locale.cons]/7); the destructor releases a reference
    //     ([locale.cons]/9): no-op.
    if(
      symbol.value.is_nil() &&
      (name == "std::__1::ios_base::init(this,ptr_void)" ||
       name == "std::__1::ios_base::~ios_base(this)" ||
       name == "std::__1::ios_base::clear(this,unsigned_int)" ||
       name == "std::__1::ios_base::getloc($constthis)" ||
       name.find("std::__1::locale::locale(this") == 0 ||
       name == "std::__1::locale::~locale(this)"))
    {
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      code_blockt block;
      const auto assign_members =
        [&](const std::map<std::string, std::function<exprt(const typet &)>>
              &values)
      {
        if(params.empty() || params[0].type().id() != ID_pointer)
          return;
        const symbol_exprt this_expr{
          params[0].get_identifier(), params[0].type()};
        const typet &base_t = to_pointer_type(params[0].type()).base_type();
        if(base_t.id() != ID_struct_tag)
          return;
        const struct_typet &st = ns.follow_tag(to_struct_tag_type(base_t));
        for(const auto &comp : st.components())
        {
          const auto v_it = values.find(id2string(comp.get_base_name()));
          if(v_it == values.end())
            continue;
          block.add(code_frontend_assignt{
            member_exprt{
              dereference_exprt{this_expr}, comp.get_name(), comp.type()},
            v_it->second(comp.type())});
        }
      };
      const auto zero = [](const typet &t) -> exprt
      {
        if(t.id() == ID_pointer)
          return null_pointer_exprt{to_pointer_type(t)};
        return from_integer(0, t);
      };
      if(
        name == "std::__1::ios_base::init(this,ptr_void)" && params.size() == 2)
      {
        const symbol_exprt sb{params[1].get_identifier(), params[1].type()};
        const auto state = [&](const typet &t) -> exprt
        {
          // goodbit = 0, badbit = 0x1 (libc++ <ios>)
          return if_exprt{
            equal_exprt{sb, null_pointer_exprt{to_pointer_type(sb.type())}},
            from_integer(1, t),
            from_integer(0, t)};
        };
        assign_members(
          {{"__rdbuf_",
            [&](const typet &t) -> exprt
            { return typecast_exprt::conditional_cast(sb, t); }},
           {"__rdstate_", state},
           {"__exceptions_", zero},
           // skipws = 0x1000, dec = 0x0002 (libc++ <ios>)
           {"__fmtflags_",
            [](const typet &t) -> exprt { return from_integer(0x1002, t); }},
           {"__width_", zero},
           {"__precision_",
            [](const typet &t) -> exprt { return from_integer(6, t); }},
           {"__loc_", zero},
           {"__fn_", zero},
           {"__index_", zero},
           {"__event_size_", zero},
           {"__event_cap_", zero},
           {"__iarray_", zero},
           {"__iarray_size_", zero},
           {"__iarray_cap_", zero},
           {"__parray_", zero},
           {"__parray_size_", zero},
           {"__parray_cap_", zero}});
      }
      else if(
        name == "std::__1::ios_base::clear(this,unsigned_int)" &&
        params.size() == 2)
      {
        // [iostate.flags]/4: rdstate() == state if rdbuf() is not null,
        // otherwise state | badbit.  (If then rdstate() & exceptions() is
        // not zero, basic_ios::failure is thrown; with the exceptions() ==
        // goodbit of Table 128 and no model of exceptions(iostate) that is
        // not reached here.)
        const symbol_exprt state{params[1].get_identifier(), params[1].type()};
        const symbol_exprt this_expr{
          params[0].get_identifier(), params[0].type()};
        const typet &base_t = to_pointer_type(params[0].type()).base_type();
        exprt rdbuf = nil_exprt{};
        if(base_t.id() == ID_struct_tag)
        {
          for(const auto &comp :
              ns.follow_tag(to_struct_tag_type(base_t)).components())
          {
            if(id2string(comp.get_base_name()) == "__rdbuf_")
              rdbuf = member_exprt{
                dereference_exprt{this_expr}, comp.get_name(), comp.type()};
          }
        }
        if(rdbuf.is_nil())
          continue;
        assign_members(
          {{"__rdstate_",
            [&](const typet &t) -> exprt
            {
              const exprt s = typecast_exprt::conditional_cast(state, t);
              return if_exprt{
                equal_exprt{
                  rdbuf, null_pointer_exprt{to_pointer_type(rdbuf.type())}},
                bitor_exprt{s, from_integer(1, t)},
                s};
            }}});
      }
      else if(name == "std::__1::ios_base::getloc($constthis)")
      {
        // [ios.base.locales]/4: the imbued locale -- the global "C" locale
        // (a null __locale_, see init above) as no imbue is modelled
        const typet &ret = to_code_type(symbol.type).return_type();
        if(ret.id() != ID_struct_tag)
          continue;
        const auto value = ::zero_initializer(ret, symbol.location, ns);
        if(!value.has_value())
          continue;
        // returned through a local object: a class prvalue is returned by
        // copy-initializing the result object from an lvalue
        const irep_idt local_id = id2string(symbol.name) + "::__cbmc_locale";
        if(!symbol_table.has_symbol(local_id))
        {
          symbolt local;
          local.name = local_id;
          local.base_name = "__cbmc_locale";
          local.type = ret;
          local.mode = symbol.mode;
          local.is_lvalue = true;
          local.is_thread_local = true;
          local.is_file_local = true;
          local.location = symbol.location;
          symbol_table.insert(std::move(local));
        }
        const symbol_exprt local_expr{local_id, ret};
        block.add(code_frontend_declt{local_expr});
        block.add(code_frontend_assignt{local_expr, *value});
        block.add(code_frontend_returnt{local_expr});
      }
      else if(name == "std::__1::locale::locale(this)")
        assign_members({{"__locale_", zero}});
      else if(
        name.find("std::__1::locale::locale(this,") == 0 &&
        params.size() == 2 && is_reference(params[1].type()))
      {
        // the copy constructor: the other locale's implementation
        const symbol_exprt other{params[1].get_identifier(), params[1].type()};
        const typet &locale_t = to_reference_type(other.type()).base_type();
        const typet &this_t = to_pointer_type(params[0].type()).base_type();
        // only the copy constructor (a reference to locale itself)
        if(
          locale_t.id() != ID_struct_tag || this_t.id() != ID_struct_tag ||
          to_struct_tag_type(locale_t).get_identifier() !=
            to_struct_tag_type(this_t).get_identifier())
        {
          continue;
        }
        {
          const struct_typet &st = ns.follow_tag(to_struct_tag_type(locale_t));
          for(const auto &comp : st.components())
          {
            if(id2string(comp.get_base_name()) != "__locale_")
              continue;
            assign_members(
              {{"__locale_",
                [&](const typet &) -> exprt
                {
                  return member_exprt{
                    dereference_exprt{other}, comp.get_name(), comp.type()};
                }}});
          }
        }
      }
      else if(name.find("std::__1::locale::locale(this,") == 0)
      {
        // other constructors (named locales, facet combination): not
        // modelled -- keep no body
        continue;
      }
      symbol.value = block;
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }

    // libc++ declares std::__sort<__less<T> &, T *> for the arithmetic types
    // T `extern template' (__algorithm/sort.h) and DEFINES the template only
    // in libc++.so (src/algorithm.cpp), so std::sort on such a range calls a
    // function without a body.  N5008 [alg.sort]/1-3: sort permutes [first,
    // last) into non-decreasing order with respect to comp; __less<T> is
    // `a < b' on the arithmetic T.  Model it as an insertion sort (the
    // complexity bound of /3 is not observable).
    if(
      symbol.value.is_nil() && name.find("std::__1::__sort<") == 0 &&
      to_code_type(symbol.type).parameters().size() == 3)
    {
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      const typet &ptr_type = params[0].type();
      if(
        ptr_type.id() == ID_pointer && params[1].type() == ptr_type &&
        (to_pointer_type(ptr_type).base_type().id() == ID_signedbv ||
         to_pointer_type(ptr_type).base_type().id() == ID_unsignedbv ||
         to_pointer_type(ptr_type).base_type().id() == ID_floatbv))
      {
        const typet &value_type = to_pointer_type(ptr_type).base_type();
        const auto local = [&](const std::string &base, const typet &type)
        {
          const irep_idt id = id2string(symbol.name) + "::" + base;
          if(!symbol_table.has_symbol(id))
          {
            symbolt local_symbol;
            local_symbol.name = id;
            local_symbol.base_name = base;
            local_symbol.type = type;
            local_symbol.mode = symbol.mode;
            local_symbol.is_lvalue = true;
            local_symbol.is_thread_local = true;
            local_symbol.is_file_local = true;
            local_symbol.location = symbol.location;
            symbol_table.insert(std::move(local_symbol));
          }
          return symbol_exprt{id, type};
        };
        const symbol_exprt first{params[0].get_identifier(), ptr_type};
        const symbol_exprt last{params[1].get_identifier(), ptr_type};
        const symbol_exprt i = local("__cbmc_i", ptr_type);
        const symbol_exprt j = local("__cbmc_j", ptr_type);
        const symbol_exprt t = local("__cbmc_t", value_type);
        const exprt one = from_integer(1, signed_size_type());
        const exprt prev = dereference_exprt{minus_exprt{j, one}};

        // while(j != first && *j < *(j - 1)) { swap; --j; }
        code_blockt swap_block;
        swap_block.add(code_frontend_assignt{t, dereference_exprt{j}});
        swap_block.add(code_frontend_assignt{dereference_exprt{j}, prev});
        swap_block.add(code_frontend_assignt{prev, t});
        swap_block.add(code_frontend_assignt{j, minus_exprt{j, one}});
        code_blockt outer_body;
        outer_body.add(code_frontend_assignt{j, i});
        outer_body.add(code_whilet{
          and_exprt{
            notequal_exprt{j, first},
            binary_relation_exprt{dereference_exprt{j}, ID_lt, prev}},
          std::move(swap_block)});
        outer_body.add(code_frontend_assignt{i, plus_exprt{i, one}});

        code_blockt sorted;
        sorted.add(code_frontend_assignt{i, plus_exprt{first, one}});
        sorted.add(code_whilet{notequal_exprt{i, last}, std::move(outer_body)});

        code_blockt block;
        block.add(code_frontend_declt{i});
        block.add(code_frontend_declt{j});
        block.add(code_frontend_declt{t});
        block.add(
          code_ifthenelset{notequal_exprt{first, last}, std::move(sorted)});
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
        continue;
      }
    }

    // N5008 [locale.general]/8: the program-startup global locale is the
    // "C" locale, and libstdc++ initialises it inside the shared library
    // where CBMC cannot see it.  Give the default constructor, the
    // copy-reference management and the destructor empty bodies (the model
    // facet below carries the actual classification data), and let
    // __try_use_facet<ctype<char>> return the modelled classic facet
    // instead of reading the invisible _M_impl->_M_facets table.
    if(
      name == "std::locale::locale(this)" ||
      name == "std::locale::~locale(this)")
    {
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }
    if(base == "Init" && name.find("ios_base") != std::string::npos)
    {
      // ios_base::Init constructor — provide empty body.
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }
    if(base == "_M_init" && name.find("std::ios_base::_M_init") == 0)
    {
      // std::ios_base::_M_init is defined in libstdc++'s compiled
      // library (src/c++98/ios_locale.cc); it establishes the
      // [basic.ios.cons] Table postconditions that basic_ios::init()
      // delegates: precision() == 6, width() == 0, flags() ==
      // skipws|dec, exceptions() == goodbit, rdstate() == goodbit.
      // Synthesize exactly those member assignments (_Ios_Fmtflags:
      // _S_dec = 1<<1, _S_skipws = 1<<12).
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      code_blockt block;
      if(params.size() == 1 && params[0].type().id() == ID_pointer)
      {
        const symbol_exprt this_expr{
          params[0].get_identifier(), params[0].type()};
        const typet &base_t = to_pointer_type(params[0].type()).base_type();
        if(base_t.id() == ID_struct_tag)
        {
          const struct_typet &st = ns.follow_tag(to_struct_tag_type(base_t));
          const std::map<std::string, mp_integer> values = {
            {"_M_precision", 6},
            {"_M_width", 0},
            {"_M_flags", (mp_integer(1) << 1) + (mp_integer(1) << 12)},
            {"_M_exception", 0},
            {"_M_streambuf_state", 0}};
          for(const auto &comp : st.components())
          {
            auto v_it = values.find(id2string(comp.get_base_name()));
            if(v_it == values.end())
              continue;
            const member_exprt lhs{
              dereference_exprt{this_expr}, comp.get_name(), comp.type()};
            exprt rhs;
            if(comp.type().id() == ID_c_enum_tag)
            {
              rhs = typecast_exprt{
                from_integer(
                  v_it->second,
                  ns.follow_tag(to_c_enum_tag_type(comp.type()))
                    .underlying_type()),
                comp.type()};
            }
            else
            {
              rhs = from_integer(v_it->second, comp.type());
            }
            block.add(code_frontend_assignt{lhs, rhs});
          }
        }
      }
      symbol.value = block;
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }
    if(
      (base == "locale" || base == "~locale") &&
      name.find("std::locale::") == 0 && symbol.value.is_nil())
    {
      // std::locale's constructors and destructor are defined in
      // libstdc++'s compiled library (src/c++98/locale_init.cc), so
      // CBMC sees no body and havocs every object holding a locale
      // (each stream buffer does).  The locale's only data member is
      // the _Impl pointer; CBMC models all facet access of the global
      // "C" locale through __try_use_facet (see
      // provide_classic_ctype_char_model), so the pointer merely needs
      // to be DETERMINATE: a null _M_impl denotes the modeled global
      // locale.
      //   default ctor ([locale.cons]/2, a copy of the global locale):
      //     this->_M_impl = 0
      //   copy ctor ([locale.cons]/7):  this->_M_impl = other._M_impl
      //   destructor ([locale.cons]/9, releases a reference): no-op
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      code_blockt block;
      if(
        base == "locale" && !params.empty() &&
        params[0].type().id() == ID_pointer)
      {
        const symbol_exprt this_expr{
          params[0].get_identifier(), params[0].type()};
        const typet &base_t = to_pointer_type(params[0].type()).base_type();
        if(base_t.id() == ID_struct_tag)
        {
          const struct_typet &st = ns.follow_tag(to_struct_tag_type(base_t));
          for(const auto &comp : st.components())
          {
            if(id2string(comp.get_base_name()) != "_M_impl")
              continue;
            const member_exprt lhs{
              dereference_exprt{this_expr}, comp.get_name(), comp.type()};
            if(params.size() == 1)
            {
              // default constructor
              block.add(code_frontend_assignt{
                lhs, null_pointer_exprt{to_pointer_type(comp.type())}});
            }
            else if(
              params.size() == 2 && params[1].type().id() == ID_pointer &&
              to_pointer_type(params[1].type()).base_type() == base_t)
            {
              // copy constructor
              const symbol_exprt other_expr{
                params[1].get_identifier(), params[1].type()};
              const member_exprt rhs{
                dereference_exprt{other_expr}, comp.get_name(), comp.type()};
              block.add(code_frontend_assignt{lhs, rhs});
            }
            break;
          }
        }
      }
      symbol.value = block;
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }
    if(base == "_M_id" && name.find("std::locale::id::_M_id") == 0)
    {
      // std::locale::id::_M_id() is defined in the compiled library;
      // it lazily assigns and returns the facet's index into the
      // locale's facet table.  CBMC does not model the facet table
      // (all lookup goes through the modeled __try_use_facet), so
      // returning the stored index deterministically is sufficient.
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      code_blockt block;
      if(!params.empty() && params[0].type().id() == ID_pointer)
      {
        const symbol_exprt this_expr{
          params[0].get_identifier(), params[0].type()};
        const typet &base_t = to_pointer_type(params[0].type()).base_type();
        if(base_t.id() == ID_struct_tag)
        {
          const struct_typet &st = ns.follow_tag(to_struct_tag_type(base_t));
          for(const auto &comp : st.components())
          {
            if(id2string(comp.get_base_name()) != "_M_index")
              continue;
            const member_exprt idx{
              dereference_exprt{this_expr}, comp.get_name(), comp.type()};
            const typet &ret = to_code_type(symbol.type).return_type();
            block.add(code_frontend_returnt{
              idx.type() == ret
                ? static_cast<exprt>(idx)
                : static_cast<exprt>(typecast_exprt{idx, ret})});
            break;
          }
        }
      }
      symbol.value = block;
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }
    if(
      (base == "ios_base" || base == "~ios_base") &&
      name.find("std::ios_base::") == 0)
    {
      // libstdc++ defines std::ios_base's constructor and destructor in
      // its compiled library (src/c++98/ios_init.cc); the headers only
      // declare them, so CBMC sees no body and havocs every stream's
      // construction/destruction.  N5008 [ios.base.cons]/1: after the
      // ios_base() constructor each member has an INDETERMINATE value
      // (basic_ios::init() establishes the post-conditions later) -- an
      // empty body is exactly conformant.  ~ios_base only services
      // callbacks registered via register_callback ([ios.base.callback])
      // and locale bookkeeping; CBMC's model registers none, so an empty
      // body is a sound model of the destruction itself.
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }
    if(
      base == "_S_copy_chars" && name.find("basic_string") != std::string::npos)
    {
      // _S_copy_chars(p, k1, k2) copies characters from [k1,k2) to p.
      // For pointer iterators this is memcpy(p, k1, k2-k1).
      // Provide an empty body — the copy is not needed for verification
      // of string size/length properties.
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
      continue;
    }

    if(base == "_S_relocate" && name.find("vector") != std::string::npos)
    {
      // _S_relocate(first, last, result, alloc) → copy [first,last) to
      // result, return result + (last - first).
      // Uses __CPROVER_array_replace to copy the source object's
      // content into the destination object.
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      if(params.size() >= 3)
      {
        symbol_exprt first(params[0].get_identifier(), params[0].type());
        symbol_exprt last(params[1].get_identifier(), params[1].type());
        symbol_exprt result(params[2].get_identifier(), params[2].type());
        const auto &ret_type = to_code_type(symbol.type).return_type();
        minus_exprt diff(last, first);
        diff.type() = pointer_diff_type();
        plus_exprt sum(result, diff);
        sum.type() = ret_type;
        code_blockt copy_block;
        copy_block.add(codet{ID_array_replace, {result, first}});
        copy_block.add(code_frontend_returnt{sum});
        code_blockt block;
        block.add(code_ifthenelset{
          notequal_exprt{first, last},
          std::move(copy_block),
          code_frontend_returnt{result}});
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
      continue;
    }

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
    else if(base == "_Rb_tree_insert_and_rebalance")
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_rb_insert_and_rebalance_body(symbol, ns);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(base == "_Rb_tree_increment")
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_rb_increment_body(symbol, ns, symbol_table);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(base == "_Rb_tree_decrement")
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_rb_decrement_body(symbol, ns, symbol_table);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(base == "_Rb_tree_rebalance_for_erase")
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_rb_rebalance_for_erase_body(symbol, ns, symbol_table);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base == "_M_next_bkt" &&
      name.find("_Prime_rehash_policy") != std::string::npos)
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_prime_next_bkt_body(symbol, ns);
      if(!body.statements().empty())
      {
        symbol.value = std::move(body);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base == "_M_need_rehash" &&
      name.find("_Prime_rehash_policy") != std::string::npos)
    {
      ensure_parameter_symbols(symbol, symbol_table);
      auto body = make_prime_need_rehash_body(symbol, ns);
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
      (base == "logic_error" || base == "runtime_error" ||
       base == "~logic_error" || base == "~runtime_error" ||
       base == "~length_error" || base == "~out_of_range" ||
       base == "~invalid_argument" || base == "~domain_error" ||
       base == "~range_error" || base == "~overflow_error" ||
       base == "~underflow_error") &&
      name.find("std::") == 0 && symbol.value.is_nil())
    {
      // libc++ defines these exception constructors/destructors in its
      // compiled library (_LIBCPP_EXPORTED_FROM_ABI); libstdc++'s are
      // header-inline.  [stdexcept]: the constructors store the
      // message (observable only through what()); an empty body is a
      // sufficient model for verification of non-throwing paths, and
      // throwing paths fail visibly at the throw itself.
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = code_blockt();
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
    }
    else if(
      base == "max_size" && symbol.value.is_nil() &&
      name.find("vector<") != std::string::npos &&
      to_code_type(symbol.type).return_type().id() != ID_auto &&
      !to_code_type(symbol.type).parameters().empty())
    {
      // libc++'s vector::max_size (vector:603) can be left bodyless
      // when its eager conversion is absorbed during instantiation;
      // __recommend then calls a no-body function and every push_back
      // havocs.  [vector.capacity]/1 with the default allocator
      // ([allocator.traits.members]/6: SIZE_MAX / sizeof(value_type),
      // capped by numeric_limits<difference_type>::max()): synthesize
      // exactly that constant.
      const typet &ret = to_code_type(symbol.type).return_type();
      const typet &this_t = to_code_type(symbol.type).parameters()[0].type();
      if(
        ret.id() == ID_unsignedbv && this_t.id() == ID_pointer &&
        to_pointer_type(this_t).base_type().id() == ID_struct_tag)
      {
        const symbolt *class_sym = symbol_table.lookup(
          to_struct_tag_type(to_pointer_type(this_t).base_type())
            .get_identifier());
        if(
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil())
        {
          const auto &targs = static_cast<const cpp_template_args_tct &>(
            class_sym->type.find(ID_C_template_arguments));
          if(!targs.arguments().empty() && targs.arguments()[0].id() == ID_type)
          {
            auto elem_size = size_of_expr(targs.arguments()[0].type(), ns);
            const auto elem_size_int = elem_size.has_value()
                                         ? numeric_cast<mp_integer>(*elem_size)
                                         : std::optional<mp_integer>{};
            if(elem_size_int.has_value() && *elem_size_int > 0)
            {
              const std::size_t width = to_unsignedbv_type(ret).get_width();
              const mp_integer size_max = power(2, width) - 1;
              const mp_integer ptrdiff_max = power(2, width - 1) - 1;
              const mp_integer value =
                std::min(size_max / *elem_size_int, ptrdiff_max);
              code_blockt block;
              block.add(code_frontend_returnt{from_integer(value, ret)});
              ensure_parameter_symbols(symbol, symbol_table);
              symbol.value = std::move(block);
              symbol.value.type() = symbol.type;
              deferred_typechecking.erase(symbol.name);
            }
          }
        }
      }
    }
    else if(
      base.find("__libcpp_operator_new") == 0 && name.find("std::") == 0 &&
      symbol.value.is_nil())
    {
      // libc++'s allocation trampoline (new:269) forwards a variadic
      // pack to clang's __builtin_operator_new; the instance can be
      // left bodyless when its eager conversion is absorbed by
      // candidate matching, so every container allocation returned an
      // unconstrained (possibly null) pointer.  Its semantics are
      // those of ::operator new ([new.delete.single]: returns a
      // non-null pointer to storage of the requested size, or
      // throws); model it with CBMC's allocator, exactly as
      // allocator_traits::allocate above.
      const code_typet &fn_type = to_code_type(symbol.type);
      const auto &params = fn_type.parameters();
      if(!params.empty())
      {
        const symbol_exprt size_expr(
          params[0].get_identifier(), params[0].type());
        const typet ret_type = pointer_type(empty_typet{});
        side_effect_exprt alloc{
          ID_allocate, {size_expr, false_exprt()}, ret_type, symbol.location};
        code_blockt block;
        block.add(code_frontend_returnt(alloc));
        ensure_parameter_symbols(symbol, symbol_table);
        // The return type may still carry an undeduced `auto`
        // (the failed conversion never deduced it); pin it to void*.
        to_code_type(symbol.type).return_type() = ret_type;
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      base.find("__libcpp_operator_delete") == 0 && name.find("std::") == 0 &&
      symbol.value.is_nil())
    {
      // ::operator delete semantics; no-op for verification, exactly
      // as allocator_traits::deallocate above.
      code_blockt block;
      ensure_parameter_symbols(symbol, symbol_table);
      if(to_code_type(symbol.type).return_type().id() == ID_auto)
        to_code_type(symbol.type).return_type() = empty_typet{};
      symbol.value = std::move(block);
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
    }
    else if(
      base == "allocate" && name.find("__new_allocator") != std::string::npos)
    {
      // __new_allocator::allocate(n) — GCC 15+ calls this directly.
      // Same model as allocator_traits::allocate.
      const code_typet &fn_type = to_code_type(symbol.type);
      const auto &ret_type = fn_type.return_type();
      if(ret_type.id() == ID_pointer)
      {
        const auto &params = fn_type.parameters();
        // params: this, n, [hint]
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
      base == "deallocate" && name.find("__new_allocator") != std::string::npos)
    {
      // __new_allocator::deallocate — no-op for verification
      code_blockt block;
      ensure_parameter_symbols(symbol, symbol_table);
      symbol.value = std::move(block);
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
    }

    else if(
      base == "__destroy" && name.find("_Destroy_aux") != std::string::npos)
    {
      // _Destroy_aux<false>::__destroy(first, last) — no-op for
      // trivially destructible types
      ensure_parameter_symbols(symbol, symbol_table);
      code_blockt block;
      symbol.value = std::move(block);
      symbol.value.type() = symbol.type;
      deferred_typechecking.erase(symbol.name);
    }
    else if(
      base == "construct" &&
      (name.find("allocator_traits") != std::string::npos ||
       name.find("__alloc_traits") != std::string::npos ||
       name.find("__new_allocator") != std::string::npos))
    {
      // construct(alloc&, ptr, arg) → *ptr = arg
      // For a SINGLE argument of the constructed type itself, placement new
      // is equivalent to assignment.  Only then: with several forwarded
      // arguments (e.g. map's piecewise construction
      // `construct(alloc, ptr, piecewise_construct, tuple1, tuple2)`) or an
      // argument of a different type, the value must go through overload
      // resolution of _Tp's constructors ([expr.new], [over.match.ctor]) --
      // the blanket `*ptr = args[0]` model would assign a
      // piecewise_construct_t into a pair (a type-inconsistent assignment
      // that aborts symbolic execution).  In those cases leave the real
      // header body in place.
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      if(params.size() == 3)
      {
        // params[0] = allocator&, params[1] = T*, params[2] = T&&
        const auto &ptr_param = params[1];
        const auto &val_param = params[2];
        typet pointee = to_pointer_type(ptr_param.type()).base_type();
        typet val_base = val_param.type();
        if(val_base.id() == ID_pointer && val_base.get_bool("#reference"))
          val_base = to_pointer_type(val_base).base_type();
        typet pointee_cmp = pointee;
        typet val_cmp = val_base;
        pointee_cmp.remove(ID_C_constant);
        val_cmp.remove(ID_C_constant);
        if(pointee_cmp == val_cmp)
        {
          symbol_exprt ptr_sym(ptr_param.get_identifier(), ptr_param.type());
          symbol_exprt val_sym(val_param.get_identifier(), val_param.type());
          // *ptr = val (dereference the rvalue reference)
          dereference_exprt deref(ptr_sym, pointee);
          dereference_exprt val_deref(val_sym, val_base);
          code_blockt block;
          block.add(code_frontend_assignt(deref, val_deref));
          symbol.value = std::move(block);
          symbol.value.type() = symbol.type;
          deferred_typechecking.erase(symbol.name);
        }
      }
    }
    else if(
      (base == "isfinite" || base == "isinf" || base == "isnan" ||
       base == "isnormal") &&
      name.find("std::") != std::string::npos)
    {
      // std::isfinite/isinf/isnan/isnormal → CPROVER built-in expressions
      ensure_parameter_symbols(symbol, symbol_table);
      const auto &params = to_code_type(symbol.type).parameters();
      if(params.size() == 1)
      {
        symbol_exprt arg(params[0].get_identifier(), params[0].type());
        exprt result;
        if(base == "isfinite")
          result = isfinite_exprt(arg);
        else if(base == "isinf")
          result = isinf_exprt(arg);
        else if(base == "isnan")
          result = isnan_exprt(arg);
        else
          result = isnormal_exprt(arg);
        const auto &ret_type = to_code_type(symbol.type).return_type();
        code_blockt block;
        block.add(code_frontend_returnt(
          typecast_exprt::conditional_cast(result, ret_type)));
        symbol.value = std::move(block);
        symbol.value.type() = symbol.type;
        deferred_typechecking.erase(symbol.name);
      }
    }
    else if(
      (base == "move" || base == "forward" ||
       base.compare(0, 5, "move<") == 0 ||
       base.compare(0, 8, "forward<") == 0) &&
      name.find("std::") != std::string::npos && symbol.value.is_nil() &&
      symbol.type.id() == ID_code &&
      to_code_type(symbol.type).parameters().size() == 1)
    {
      // N5008 [forward]/4-5: std::move(t) is exactly
      // static_cast<remove_reference_t<T>&&>(t) and std::forward<T>(t)
      // is static_cast<T&&>(t).  The libc++ headers can leave these as
      // DECLARATIONS in translation paths where the definition is
      // elided (clang guarantees the cast semantics via its builtin
      // std-move treatment); a bodyless instance here turned every
      // moved-through value nondet (the whole vector push_back family:
      // size() read garbage).  Synthesize the cast body.
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
} // NOLINT(readability/fn_size)
