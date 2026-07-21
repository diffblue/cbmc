/// \file
/// Provide bodies for standard library functions that are declared
/// in headers but defined in libstdc++.so / libc++.so.

/// Author: Michael Tautschnig

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

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
/// table (translation unit does not use <locale>).
static exprt provide_classic_ctype_char_model(
  symbol_table_baset &symbol_table,
  const namespacet &ns)
{
  const irep_idt facet_symbol_name = "std::__CPROVER_classic_ctype_char";
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
    "std::__CPROVER_classic_ctype_table", table_type, ID_cpp};
  table_symbol.base_name = "__CPROVER_classic_ctype_table";
  table_symbol.pretty_name = table_symbol.base_name;
  table_symbol.value = std::move(table_value);
  table_symbol.is_static_lifetime = true;
  table_symbol.is_lvalue = true;
  table_symbol.type.set(ID_C_constant, true);
  symbolt *table_ptr = nullptr;
  symbol_table.move(table_symbol, table_ptr);

  // The facet object: zero-initialised ctype<char> with _M_table pointing
  // at the classification table.  The zeroed remainder is never used:
  // ctype<char>::is reads only _M_table, and no virtual dispatch happens
  // on this object.
  const struct_tag_typet facet_type{ctype_char->name};
  auto facet_zero = zero_initializer(facet_type, ctype_char->location, ns);
  if(!facet_zero.has_value())
    return nil_exprt{};

  const address_of_exprt table_address{
    index_exprt{table_ptr->symbol_expr(), from_integer(0, c_index_type())}};

  // Set the _M_table component (wherever it sits, including inside a base
  // class component) to the table's address.
  std::function<bool(exprt &, const typet &)> set_m_table =
    [&](exprt &value, const typet &type) -> bool
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
      if(
        cname == "_M_table" ||
        (cname.size() > 10 &&
         cname.compare(cname.size() - 10, 10, "::_M_table") == 0))
      {
        value.operands()[op_index] =
          typecast_exprt::conditional_cast(table_address, component.type());
        return true;
      }
      if(set_m_table(value.operands()[op_index], component.type()))
        return true;
      ++op_index;
    }
    return false;
  };
  if(!set_m_table(*facet_zero, facet_type))
    return nil_exprt{};

  symbolt facet_symbol{facet_symbol_name, facet_type, ID_cpp};
  facet_symbol.base_name = "__CPROVER_classic_ctype_char";
  facet_symbol.pretty_name = facet_symbol.base_name;
  facet_symbol.value = std::move(*facet_zero);
  facet_symbol.is_static_lifetime = true;
  facet_symbol.is_lvalue = true;
  symbolt *facet_ptr = nullptr;
  symbol_table.move(facet_symbol, facet_ptr);
  return facet_ptr->symbol_expr();
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
  //   if (__p == &__header) { __header._M_parent = __x; __header._M_right = __x; }
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
    auto zero = zero_initializer(ret_type, symbol.location, ns);
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
    // (except for specific functions we need to override)
    if(symbol.value.is_not_nil() && !is_deferred)
    {
      if(
        base.find("__try_use_facet") == 0 &&
        name.find("<std::tag-ctype<char>>") != std::string::npos &&
        to_code_type(symbol.type).return_type().id() == ID_pointer)
      {
        // Override the header-inline body, which reads the invisible
        // libstdc++-internal __loc->_M_impl->_M_facets table, with a
        // return of the modelled classic-"C" ctype<char> facet
        // ([locale.general]/8: the startup global locale is the "C"
        // locale).  See provide_classic_ctype_char_model.
        exprt facet = provide_classic_ctype_char_model(symbol_table, ns);
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
