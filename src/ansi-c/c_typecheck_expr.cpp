/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#include "c_typecheck_base.h"

#include <sstream>

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/string_constant.h>
#include <util/suffix.h>

#include <goto-programs/adjust_float_expressions.h>

#include "anonymous_member.h"
#include "ansi_c_declaration.h"
#include "builtin_factory.h"
#include "c_expr.h"
#include "c_qualifiers.h"
#include "expr2c.h"
#include "padding.h"
#include "type2name.h"

void c_typecheck_baset::typecheck_expr(exprt &expr)
{
  if(expr.id()==ID_already_typechecked)
  {
    expr.swap(to_already_typechecked_expr(expr).get_expr());
    return;
  }

  // first do sub-nodes
  typecheck_expr_operands(expr);

  // now do case-split
  typecheck_expr_main(expr);
}

void c_typecheck_baset::add_rounding_mode(exprt &expr)
{
  for(auto &op : expr.operands())
    add_rounding_mode(op);

  if(expr.id()==ID_div ||
     expr.id()==ID_mult ||
     expr.id()==ID_plus ||
     expr.id()==ID_minus)
  {
    if(expr.type().id()==ID_floatbv &&
       expr.operands().size()==2)
    {
      // The rounding mode to be used at compile time is non-obvious.
      // We'll simply use round to even (0), which is suggested
      // by Sec. F.7.2 Translation, ISO-9899:1999.
      expr.operands().resize(3);

      if(expr.id()==ID_div)
        expr.id(ID_floatbv_div);
      else if(expr.id()==ID_mult)
        expr.id(ID_floatbv_mult);
      else if(expr.id()==ID_plus)
        expr.id(ID_floatbv_plus);
      else if(expr.id()==ID_minus)
        expr.id(ID_floatbv_minus);
      else
        UNREACHABLE;

      to_ieee_float_op_expr(expr).rounding_mode() =
        from_integer(0, unsigned_int_type());
    }
  }
}

bool c_typecheck_baset::gcc_types_compatible_p(
  const typet &type1,
  const typet &type2)
{
  // read
  // http://gcc.gnu.org/onlinedocs/gcc-3.3.6/gcc/Other-Builtins.html

  // check qualifiers first
  if(c_qualifierst(type1)!=c_qualifierst(type2))
    return false;

  if(type1.id()==ID_c_enum_tag)
    return gcc_types_compatible_p(follow_tag(to_c_enum_tag_type(type1)), type2);
  else if(type2.id()==ID_c_enum_tag)
    return gcc_types_compatible_p(type1, follow_tag(to_c_enum_tag_type(type2)));

  if(type1.id()==ID_c_enum)
  {
    if(type2.id()==ID_c_enum) // both are enums
      return type1==type2; // compares the tag
    else if(type2 == to_c_enum_type(type1).underlying_type())
      return true;
  }
  else if(type2.id()==ID_c_enum)
  {
    if(type1 == to_c_enum_type(type2).underlying_type())
      return true;
  }
  else if(type1.id()==ID_pointer &&
          type2.id()==ID_pointer)
  {
    return gcc_types_compatible_p(
      to_pointer_type(type1).base_type(), to_pointer_type(type2).base_type());
  }
  else if(type1.id()==ID_array &&
          type2.id()==ID_array)
  {
    return gcc_types_compatible_p(
      to_array_type(type1).element_type(),
      to_array_type(type2).element_type()); // ignore size
  }
  else if(type1.id()==ID_code &&
          type2.id()==ID_code)
  {
    const code_typet &c_type1=to_code_type(type1);
    const code_typet &c_type2=to_code_type(type2);

    if(!gcc_types_compatible_p(
        c_type1.return_type(),
        c_type2.return_type()))
      return false;

    if(c_type1.parameters().size()!=c_type2.parameters().size())
      return false;

    for(std::size_t i=0; i<c_type1.parameters().size(); i++)
      if(!gcc_types_compatible_p(
          c_type1.parameters()[i].type(),
          c_type2.parameters()[i].type()))
        return false;

    return true;
  }
  else
  {
    if(type1==type2)
    {
      // Need to distinguish e.g. long int from int or
      // long long int from long int.
      // The rules appear to match those of C++.

      if(type1.get(ID_C_c_type)==type2.get(ID_C_c_type))
        return true;
    }
  }

  return false;
}

void c_typecheck_baset::typecheck_expr_main(exprt &expr)
{
  if(expr.id()==ID_side_effect)
    typecheck_expr_side_effect(to_side_effect_expr(expr));
  else if(expr.id()==ID_constant)
    typecheck_expr_constant(expr);
  else if(expr.id()==ID_infinity)
  {
    // ignore
  }
  else if(expr.id()==ID_symbol)
    typecheck_expr_symbol(expr);
  else if(expr.id()==ID_unary_plus ||
          expr.id()==ID_unary_minus ||
          expr.id()==ID_bitnot)
    typecheck_expr_unary_arithmetic(expr);
  else if(expr.id()==ID_not)
    typecheck_expr_unary_boolean(expr);
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies ||
    expr.id() == ID_xor)
    typecheck_expr_binary_boolean(expr);
  else if(expr.id()==ID_address_of)
    typecheck_expr_address_of(expr);
  else if(expr.id()==ID_dereference)
    typecheck_expr_dereference(expr);
  else if(expr.id()==ID_member)
    typecheck_expr_member(expr);
  else if(expr.id()==ID_ptrmember)
    typecheck_expr_ptrmember(expr);
  else if(expr.id()==ID_equal  ||
          expr.id()==ID_notequal ||
          expr.id()==ID_lt  ||
          expr.id()==ID_le ||
          expr.id()==ID_gt  ||
          expr.id()==ID_ge)
    typecheck_expr_rel(to_binary_relation_expr(expr));
  else if(expr.id()==ID_index)
    typecheck_expr_index(expr);
  else if(expr.id()==ID_typecast)
    typecheck_expr_typecast(expr);
  else if(expr.id()==ID_sizeof)
    typecheck_expr_sizeof(expr);
  else if(expr.id()==ID_alignof)
    typecheck_expr_alignof(expr);
  else if(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
    expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_bitand ||
    expr.id() == ID_bitxor || expr.id() == ID_bitor || expr.id() == ID_bitnand)
  {
    typecheck_expr_binary_arithmetic(expr);
  }
  else if(expr.id()==ID_shl || expr.id()==ID_shr)
    typecheck_expr_shifts(to_shift_expr(expr));
  else if(expr.id()==ID_comma)
    typecheck_expr_comma(expr);
  else if(expr.id()==ID_if)
    typecheck_expr_trinary(to_if_expr(expr));
  else if(expr.id()==ID_code)
  {
    error().source_location = expr.source_location();
    error() << "typecheck_expr_main got code: " << expr.pretty() << eom;
    throw 0;
  }
  else if(expr.id()==ID_gcc_builtin_va_arg)
    typecheck_expr_builtin_va_arg(expr);
  else if(expr.id()==ID_cw_va_arg_typeof)
    typecheck_expr_cw_va_arg_typeof(expr);
  else if(expr.id()==ID_gcc_builtin_types_compatible_p)
  {
    expr.type()=bool_typet();
    auto &subtypes =
      (static_cast<type_with_subtypest &>(expr.add(ID_type_arg))).subtypes();
    assert(subtypes.size()==2);
    typecheck_type(subtypes[0]);
    typecheck_type(subtypes[1]);
    source_locationt source_location=expr.source_location();

    // ignores top-level qualifiers
    subtypes[0].remove(ID_C_constant);
    subtypes[0].remove(ID_C_volatile);
    subtypes[0].remove(ID_C_restricted);
    subtypes[1].remove(ID_C_constant);
    subtypes[1].remove(ID_C_volatile);
    subtypes[1].remove(ID_C_restricted);

    expr = make_boolean_expr(gcc_types_compatible_p(subtypes[0], subtypes[1]));
    expr.add_source_location()=source_location;
  }
  else if(expr.id()==ID_clang_builtin_convertvector)
  {
    // This has one operand and a type, and acts like a typecast
    DATA_INVARIANT(expr.operands().size()==1, "clang_builtin_convertvector has one operand");
    typecheck_type(expr.type());
    typecast_exprt tmp(to_unary_expr(expr).op(), expr.type());
    tmp.add_source_location()=expr.source_location();
    expr.swap(tmp);
  }
  else if(expr.id()==ID_builtin_offsetof)
    typecheck_expr_builtin_offsetof(expr);
  else if(expr.id()==ID_string_constant)
  {
    // already fine -- mark as lvalue
    expr.set(ID_C_lvalue, true);
  }
  else if(expr.id()==ID_arguments)
  {
    // already fine
  }
  else if(expr.id()==ID_designated_initializer)
  {
    exprt &designator=static_cast<exprt &>(expr.add(ID_designator));

    Forall_operands(it, designator)
    {
      if(it->id()==ID_index)
        typecheck_expr(to_unary_expr(*it).op()); // still needs typechecking
    }
  }
  else if(expr.id()==ID_initializer_list)
  {
    // already fine, just set some type
    expr.type()=void_type();
  }
  else if(
    expr.id() == ID_forall || expr.id() == ID_exists || expr.id() == ID_lambda)
  {
    // These have two operands.
    // op0 is a tuple with declarations,
    // op1 is the bound expression
    auto &binary_expr = to_binary_expr(expr);
    auto &bindings = binary_expr.op0().operands();
    auto &where = binary_expr.op1();

    for(const auto &binding : bindings)
    {
      if(binding.get(ID_statement) != ID_decl)
      {
        error().source_location = expr.source_location();
        error() << "expected declaration as operand of quantifier" << eom;
        throw 0;
      }
    }

    if(has_subexpr(where, ID_side_effect))
    {
      error().source_location = expr.source_location();
      error() << "quantifier must not contain side effects" << eom;
      throw 0;
    }

    // replace declarations by symbol expressions
    for(auto &binding : bindings)
      binding = to_code_frontend_decl(to_code(binding)).symbol();

    if(expr.id() == ID_lambda)
    {
      mathematical_function_typet::domaint domain;

      for(auto &binding : bindings)
        domain.push_back(binding.type());

      expr.type() = mathematical_function_typet(domain, where.type());
    }
    else
    {
      expr.type() = bool_typet();
      implicit_typecast_bool(where);
    }
  }
  else if(expr.id()==ID_label)
  {
    expr.type()=void_type();
  }
  else if(expr.id()==ID_array)
  {
    // these pop up as string constants, and are already typed
  }
  else if(expr.id()==ID_complex)
  {
    // these should only exist as constants,
    // and should already be typed
  }
  else if(expr.id() == ID_complex_real)
  {
    const exprt &op = to_unary_expr(expr).op();

    if(op.type().id() != ID_complex)
    {
      if(!is_number(op.type()))
      {
        error().source_location = op.source_location();
        error() << "real part retrieval expects numerical operand, "
                << "but got '" << to_string(op.type()) << "'" << eom;
        throw 0;
      }

      typecast_exprt typecast_expr(op, complex_typet(op.type()));
      complex_real_exprt complex_real_expr(typecast_expr);

      expr.swap(complex_real_expr);
    }
    else
    {
      complex_real_exprt complex_real_expr(op);

      // these are lvalues if the operand is one
      if(op.get_bool(ID_C_lvalue))
        complex_real_expr.set(ID_C_lvalue, true);

      if(op.type().get_bool(ID_C_constant))
        complex_real_expr.type().set(ID_C_constant, true);

      expr.swap(complex_real_expr);
    }
  }
  else if(expr.id() == ID_complex_imag)
  {
    const exprt &op = to_unary_expr(expr).op();

    if(op.type().id() != ID_complex)
    {
      if(!is_number(op.type()))
      {
        error().source_location = op.source_location();
        error() << "real part retrieval expects numerical operand, "
                << "but got '" << to_string(op.type()) << "'" << eom;
        throw 0;
      }

      typecast_exprt typecast_expr(op, complex_typet(op.type()));
      complex_imag_exprt complex_imag_expr(typecast_expr);

      expr.swap(complex_imag_expr);
    }
    else
    {
      complex_imag_exprt complex_imag_expr(op);

      // these are lvalues if the operand is one
      if(op.get_bool(ID_C_lvalue))
        complex_imag_expr.set(ID_C_lvalue, true);

      if(op.type().get_bool(ID_C_constant))
        complex_imag_expr.type().set(ID_C_constant, true);

      expr.swap(complex_imag_expr);
    }
  }
  else if(expr.id()==ID_generic_selection)
  {
    // This is C11.
    // The operand is already typechecked. Depending
    // on its type, we return one of the generic associations.
    auto &op = to_unary_expr(expr).op();

    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(op.type().id() == ID_bool)
      op = typecast_exprt(op, signed_int_type());

    irept::subt &generic_associations=
      expr.add(ID_generic_associations).get_sub();

    // first typecheck all types
    for(auto &irep : generic_associations)
    {
      if(irep.get(ID_type_arg) != ID_default)
      {
        typet &type = static_cast<typet &>(irep.add(ID_type_arg));
        typecheck_type(type);
      }
    }

    // first try non-default match
    exprt default_match=nil_exprt();
    exprt assoc_match=nil_exprt();

    const typet &op_type = follow(op.type());

    for(const auto &irep : generic_associations)
    {
      if(irep.get(ID_type_arg) == ID_default)
        default_match = static_cast<const exprt &>(irep.find(ID_value));
      else if(
        op_type == follow(static_cast<const typet &>(irep.find(ID_type_arg))))
      {
        assoc_match = static_cast<const exprt &>(irep.find(ID_value));
      }
    }

    if(assoc_match.is_nil())
    {
      if(default_match.is_not_nil())
        expr.swap(default_match);
      else
      {
        error().source_location = expr.source_location();
        error() << "unmatched generic selection: " << to_string(op.type())
                << eom;
        throw 0;
      }
    }
    else
      expr.swap(assoc_match);

    // still need to typecheck the result
    typecheck_expr(expr);
  }
  else if(expr.id()==ID_gcc_asm_input ||
          expr.id()==ID_gcc_asm_output ||
          expr.id()==ID_gcc_asm_clobbered_register)
  {
  }
  else if(expr.id()==ID_lshr || expr.id()==ID_ashr ||
          expr.id()==ID_assign_lshr || expr.id()==ID_assign_ashr)
  {
    // already type checked
  }
  else if(expr.id() == ID_C_spec_assigns || expr.id() == ID_target_list)
  {
    // already type checked
  }
  else
  {
    error().source_location = expr.source_location();
    error() << "unexpected expression: " << expr.pretty() << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_expr_comma(exprt &expr)
{
  expr.type() = to_binary_expr(expr).op1().type();

  // make this an l-value if the last operand is one
  if(to_binary_expr(expr).op1().get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);
}

void c_typecheck_baset::typecheck_expr_builtin_va_arg(exprt &expr)
{
  // The first parameter is the va_list, and the second
  // is the type, which will need to be fixed and checked.
  // The type is given by the parser as type of the expression.

  typet arg_type=expr.type();
  typecheck_type(arg_type);

  const code_typet new_type(
    {code_typet::parametert(pointer_type(void_type()))}, std::move(arg_type));

  exprt arg = to_unary_expr(expr).op();

  implicit_typecast(arg, pointer_type(void_type()));

  symbol_exprt function(ID_gcc_builtin_va_arg, new_type);
  function.add_source_location() = expr.source_location();

  // turn into function call
  side_effect_expr_function_callt result(
    function, {arg}, new_type.return_type(), expr.source_location());

  expr.swap(result);

  // Make sure symbol exists, but we have it return void
  // to avoid collisions of the same symbol with different
  // types.

  code_typet symbol_type=new_type;
  symbol_type.return_type()=void_type();

  symbolt symbol;
  symbol.base_name=ID_gcc_builtin_va_arg;
  symbol.name=ID_gcc_builtin_va_arg;
  symbol.type=symbol_type;
  symbol.mode = ID_C;

  symbol_table.insert(std::move(symbol));
}

void c_typecheck_baset::typecheck_expr_cw_va_arg_typeof(exprt &expr)
{
  // used in Code Warrior via
  //
  // __va_arg( <Symbol>, _var_arg_typeof( <Typ> ) )
  //
  // where __va_arg is declared as
  //
  // extern void* __va_arg(void*, int);

  typet &type=static_cast<typet &>(expr.add(ID_type_arg));
  typecheck_type(type);

  // these return an integer
  expr.type()=signed_int_type();
}

void c_typecheck_baset::typecheck_expr_builtin_offsetof(exprt &expr)
{
  // these need not be constant, due to array indices!

  if(!expr.operands().empty())
  {
    error().source_location = expr.source_location();
    error() << "builtin_offsetof expects no operands" << eom;
    throw 0;
  }

  typet &type=static_cast<typet &>(expr.add(ID_type_arg));
  typecheck_type(type);

  exprt &member=static_cast<exprt &>(expr.add(ID_designator));

  exprt result=from_integer(0, size_type());

  forall_operands(m_it, member)
  {
    type = follow(type);

    if(m_it->id()==ID_member)
    {
      if(type.id()!=ID_union && type.id()!=ID_struct)
      {
        error().source_location = expr.source_location();
        error() << "offsetof of member expects struct/union type, "
                << "but got '" << to_string(type) << "'" << eom;
        throw 0;
      }

      bool found=false;
      irep_idt component_name=m_it->get(ID_component_name);

      while(!found)
      {
        assert(type.id()==ID_union || type.id()==ID_struct);

        const struct_union_typet &struct_union_type=
          to_struct_union_type(type);

        // direct member?
        if(struct_union_type.has_component(component_name))
        {
          found=true;

          if(type.id()==ID_struct)
          {
            auto o_opt =
              member_offset_expr(to_struct_type(type), component_name, *this);

            if(!o_opt.has_value())
            {
              error().source_location = expr.source_location();
              error() << "offsetof failed to determine offset of '"
                      << component_name << "'" << eom;
              throw 0;
            }

            result = plus_exprt(
              result,
              typecast_exprt::conditional_cast(o_opt.value(), size_type()));
          }

          type=struct_union_type.get_component(component_name).type();
        }
        else
        {
          // maybe anonymous?
          bool found2=false;

          for(const auto &c : struct_union_type.components())
          {
            if(
              c.get_anonymous() &&
              (c.type().id() == ID_struct_tag || c.type().id() == ID_union_tag))
            {
              if(has_component_rec(c.type(), component_name, *this))
              {
                if(type.id()==ID_struct)
                {
                  auto o_opt = member_offset_expr(
                    to_struct_type(type), c.get_name(), *this);

                  if(!o_opt.has_value())
                  {
                    error().source_location = expr.source_location();
                    error() << "offsetof failed to determine offset of '"
                            << component_name << "'" << eom;
                    throw 0;
                  }

                  result = plus_exprt(
                    result,
                    typecast_exprt::conditional_cast(
                      o_opt.value(), size_type()));
                }

                typet tmp = follow(c.type());
                type=tmp;
                assert(type.id()==ID_union || type.id()==ID_struct);
                found2=true;
                break; // we run into another iteration of the outer loop
              }
            }
          }

          if(!found2)
          {
            error().source_location = expr.source_location();
            error() << "offset-of of member failed to find component '"
                    << component_name << "' in '" << to_string(type) << "'"
                    << eom;
            throw 0;
          }
        }
      }
    }
    else if(m_it->id()==ID_index)
    {
      if(type.id()!=ID_array)
      {
        error().source_location = expr.source_location();
        error() << "offsetof of index expects array type" << eom;
        throw 0;
      }

      exprt index = to_unary_expr(*m_it).op();

      // still need to typecheck index
      typecheck_expr(index);

      auto element_size_opt =
        size_of_expr(to_array_type(type).element_type(), *this);

      if(!element_size_opt.has_value())
      {
        error().source_location = expr.source_location();
        error() << "offsetof failed to determine array element size" << eom;
        throw 0;
      }

      index = typecast_exprt::conditional_cast(index, size_type());

      result = plus_exprt(result, mult_exprt(element_size_opt.value(), index));

      typet tmp=type.subtype();
      type=tmp;
    }
  }

  // We make an effort to produce a constant,
  // but this may depend on variables
  simplify(result, *this);
  result.add_source_location()=expr.source_location();

  expr.swap(result);
}

void c_typecheck_baset::typecheck_expr_operands(exprt &expr)
{
  if(expr.id()==ID_side_effect &&
     expr.get(ID_statement)==ID_function_call)
  {
    // don't do function operand
    typecheck_expr(to_binary_expr(expr).op1()); // arguments
  }
  else if(expr.id()==ID_side_effect &&
          expr.get(ID_statement)==ID_statement_expression)
  {
    typecheck_code(to_side_effect_expr_statement_expression(expr).statement());
  }
  else if(
    expr.id() == ID_forall || expr.id() == ID_exists || expr.id() == ID_lambda)
  {
    // These introduce new symbols, which need to be added to the symbol table
    // before the second operand is typechecked.

    auto &binary_expr = to_binary_expr(expr);
    auto &bindings = binary_expr.op0().operands();

    for(auto &binding : bindings)
    {
      ansi_c_declarationt &declaration = to_ansi_c_declaration(binding);

      typecheck_declaration(declaration);

      if(declaration.declarators().size() != 1)
      {
        error().source_location = expr.source_location();
        error() << "forall/exists expects one declarator exactly" << eom;
        throw 0;
      }

      irep_idt identifier = declaration.declarators().front().get_name();

      // look it up
      symbol_tablet::symbolst::const_iterator s_it =
        symbol_table.symbols.find(identifier);

      if(s_it == symbol_table.symbols.end())
      {
        error().source_location = expr.source_location();
        error() << "failed to find bound symbol `" << identifier
                << "' in symbol table" << eom;
        throw 0;
      }

      const symbolt &symbol = s_it->second;

      if(
        symbol.is_type || symbol.is_extern || symbol.is_static_lifetime ||
        !is_complete_type(symbol.type) || symbol.type.id() == ID_code)
      {
        error().source_location = expr.source_location();
        error() << "unexpected quantified symbol" << eom;
        throw 0;
      }

      code_frontend_declt decl(symbol.symbol_expr());
      decl.add_source_location() = declaration.source_location();

      binding = decl;
    }

    typecheck_expr(binary_expr.op1());
  }
  else
  {
    Forall_operands(it, expr)
      typecheck_expr(*it);
  }
}

void c_typecheck_baset::typecheck_expr_symbol(exprt &expr)
{
  irep_idt identifier=to_symbol_expr(expr).get_identifier();

  // Is it a parameter? We do this while checking parameter lists.
  id_type_mapt::const_iterator p_it=parameter_map.find(identifier);
  if(p_it!=parameter_map.end())
  {
    // yes
    expr.type()=p_it->second;
    expr.set(ID_C_lvalue, true);
    return;
  }

  // renaming via GCC asm label
  asm_label_mapt::const_iterator entry=
    asm_label_map.find(identifier);
  if(entry!=asm_label_map.end())
  {
    identifier=entry->second;
    to_symbol_expr(expr).set_identifier(identifier);
  }

  // look it up
  const symbolt *symbol_ptr;
  if(lookup(identifier, symbol_ptr))
  {
    error().source_location = expr.source_location();
    error() << "failed to find symbol '" << identifier << "'" << eom;
    throw 0;
  }

  const symbolt &symbol=*symbol_ptr;

  if(symbol.is_type)
  {
    error().source_location = expr.source_location();
    error() << "did not expect a type symbol here, but got '"
            << symbol.display_name() << "'" << eom;
    throw 0;
  }

  // save the source location
  source_locationt source_location=expr.source_location();

  if(symbol.is_macro)
  {
    // preserve enum key
    #if 0
    irep_idt base_name=expr.get(ID_C_base_name);
    #endif

    follow_macros(expr);

    #if 0
    if(expr.id()==ID_constant &&
       !base_name.empty())
      expr.set(ID_C_cformat, base_name);
    else
    #endif
    typecheck_expr(expr);

    // preserve location
    expr.add_source_location()=source_location;
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "constant_infinity"))
  {
    expr=infinity_exprt(symbol.type);

    // put it back
    expr.add_source_location()=source_location;
  }
  else if(identifier=="__func__" ||
          identifier=="__FUNCTION__" ||
          identifier=="__PRETTY_FUNCTION__")
  {
    // __func__ is an ANSI-C standard compliant hack to get the function name
    // __FUNCTION__ and __PRETTY_FUNCTION__ are GCC-specific
    string_constantt s(source_location.get_function());
    s.add_source_location()=source_location;
    s.set(ID_C_lvalue, true);
    expr.swap(s);
  }
  else
  {
    expr=symbol.symbol_expr();

    // put it back
    expr.add_source_location()=source_location;

    if(symbol.is_lvalue)
      expr.set(ID_C_lvalue, true);

    if(expr.type().id()==ID_code) // function designator
    { // special case: this is sugar for &f
      address_of_exprt tmp(expr, pointer_type(expr.type()));
      tmp.set(ID_C_implicit, true);
      tmp.add_source_location()=expr.source_location();
      expr=tmp;
    }
  }
}

void c_typecheck_baset::typecheck_side_effect_statement_expression(
  side_effect_exprt &expr)
{
  codet &code = to_code(to_unary_expr(expr).op());

  // the type is the type of the last statement in the
  // block, but do worry about labels!

  codet &last=to_code_block(code).find_last_statement();

  irep_idt last_statement=last.get_statement();

  if(last_statement==ID_expression)
  {
    assert(last.operands().size()==1);
    exprt &op=last.op0();

    // arrays here turn into pointers (array decay)
    if(op.type().id()==ID_array)
      implicit_typecast(op, pointer_type(op.type().subtype()));

    expr.type()=op.type();
  }
  else
  {
    // we used to do this, but don't expect it any longer
    PRECONDITION(last_statement != ID_function_call);

    expr.type()=typet(ID_empty);
  }
}

void c_typecheck_baset::typecheck_expr_sizeof(exprt &expr)
{
  typet type;

  // these come in two flavors: with zero operands, for a type,
  // and with one operand, for an expression.
  PRECONDITION(expr.operands().size() <= 1);

  if(expr.operands().empty())
  {
    type.swap(static_cast<typet &>(expr.add(ID_type_arg)));
    typecheck_type(type);
  }
  else
  {
    const exprt &op = to_unary_expr(as_const(expr)).op();
    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(op.type().id() == ID_bool)
      type = signed_int_type();
    else
      type = op.type();
  }

  exprt new_expr;

  if(type.id()==ID_c_bit_field)
  {
    error().source_location = expr.source_location();
    error() << "sizeof cannot be applied to bit fields" << eom;
    throw 0;
  }
  else if(type.id() == ID_bool)
  {
    error().source_location = expr.source_location();
    error() << "sizeof cannot be applied to single bits" << eom;
    throw 0;
  }
  else if(type.id() == ID_empty)
  {
    // This is a gcc extension.
    // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
    new_expr = from_integer(1, size_type());
  }
  else
  {
    if(
      (type.id() == ID_struct_tag &&
       follow_tag(to_struct_tag_type(type)).is_incomplete()) ||
      (type.id() == ID_union_tag &&
       follow_tag(to_union_tag_type(type)).is_incomplete()) ||
      (type.id() == ID_c_enum_tag &&
       follow_tag(to_c_enum_tag_type(type)).is_incomplete()) ||
      (type.id() == ID_array && to_array_type(type).is_incomplete()))
    {
      error().source_location = expr.source_location();
      error() << "invalid application of \'sizeof\' to an incomplete type\n\t\'"
              << to_string(type) << "\'" << eom;
      throw 0;
    }

    auto size_of_opt = size_of_expr(type, *this);

    if(!size_of_opt.has_value())
    {
      error().source_location = expr.source_location();
      error() << "type has no size: " << to_string(type) << eom;
      throw 0;
    }

    new_expr = size_of_opt.value();
  }

  new_expr.swap(expr);

  expr.add(ID_C_c_sizeof_type)=type;

  // The type may contain side-effects.
  if(!clean_code.empty())
  {
    side_effect_exprt side_effect_expr(
      ID_statement_expression, void_type(), expr.source_location());
    auto decl_block=code_blockt::from_list(clean_code);
    decl_block.set_statement(ID_decl_block);
    side_effect_expr.copy_to_operands(decl_block);
    clean_code.clear();

    // We merge the side-effect into the operand of the typecast,
    // using a comma-expression.
    // I.e., (type)e becomes (type)(side-effect, e)
    // It is not obvious whether the type or 'e' should be evaluated
    // first.

    exprt comma_expr(ID_comma, expr.type());
    comma_expr.copy_to_operands(side_effect_expr, expr);
    expr.swap(comma_expr);
  }
}

void c_typecheck_baset::typecheck_expr_alignof(exprt &expr)
{
  typet argument_type;

  if(expr.operands().size()==1)
    argument_type = to_unary_expr(expr).op().type();
  else
  {
    typet &op_type=static_cast<typet &>(expr.add(ID_type_arg));
    typecheck_type(op_type);
    argument_type=op_type;
  }

  // we only care about the type
  mp_integer a=alignment(argument_type, *this);

  exprt tmp=from_integer(a, size_type());
  tmp.add_source_location()=expr.source_location();

  expr.swap(tmp);
}

void c_typecheck_baset::typecheck_expr_typecast(exprt &expr)
{
  exprt &op = to_unary_expr(expr).op();

  typecheck_type(expr.type());

  // The type may contain side-effects.
  if(!clean_code.empty())
  {
    side_effect_exprt side_effect_expr(
      ID_statement_expression, void_type(), expr.source_location());
    auto decl_block=code_blockt::from_list(clean_code);
    decl_block.set_statement(ID_decl_block);
    side_effect_expr.copy_to_operands(decl_block);
    clean_code.clear();

    // We merge the side-effect into the operand of the typecast,
    // using a comma-expression.
    // I.e., (type)e becomes (type)(side-effect, e)
    // It is not obvious whether the type or 'e' should be evaluated
    // first.

    exprt comma_expr(ID_comma, op.type());
    comma_expr.copy_to_operands(side_effect_expr, op);
    op.swap(comma_expr);
  }

  const typet expr_type = expr.type();

  if(
    expr_type.id() == ID_union_tag && expr_type != op.type() &&
    op.id() != ID_initializer_list)
  {
    // This is a GCC extension. It's either a 'temporary union',
    // where the argument is one of the member types.

    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(op.type().id() == ID_bool)
      op = typecast_exprt(op, signed_int_type());

    // we need to find a member with the right type
    const auto &union_type = follow_tag(to_union_tag_type(expr_type));
    for(const auto &c : union_type.components())
    {
      if(c.type() == op.type())
      {
        // found! build union constructor
        union_exprt union_expr(c.get_name(), op, expr.type());
        union_expr.add_source_location()=expr.source_location();
        expr=union_expr;
        expr.set(ID_C_lvalue, true);
        return;
      }
    }

    // not found, complain
    error().source_location = expr.source_location();
    error() << "type cast to union: type '" << to_string(op.type())
            << "' not found in union" << eom;
    throw 0;
  }

  // We allow (TYPE){ initializer_list }
  // This is called "compound literal", and is syntactic
  // sugar for a (possibly local) declaration.
  if(op.id()==ID_initializer_list)
  {
    // just do a normal initialization
    do_initializer(op, expr.type(), false);

    // This produces a struct-expression,
    // union-expression, array-expression,
    // or an expression for a pointer or scalar.
    // We produce a compound_literal expression.
    exprt tmp(ID_compound_literal, expr.type());
    tmp.copy_to_operands(op);

    // handle the case of TYPE being an array with unspecified size
    if(op.id()==ID_array &&
       expr.type().id()==ID_array &&
       to_array_type(expr.type()).size().is_nil())
      tmp.type()=op.type();

    expr=tmp;
    expr.set(ID_C_lvalue, true); // these are l-values
    return;
  }

  // a cast to void is always fine
  if(expr_type.id()==ID_empty)
    return;

  const typet op_type = op.type();

  // cast to same type?
  if(expr_type == op_type)
    return; // it's ok

  // vectors?

  if(expr_type.id()==ID_vector)
  {
    // we are generous -- any vector to vector is fine
    if(op_type.id()==ID_vector)
      return;
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
      return;
  }

  if(!is_numeric_type(expr_type) && expr_type.id()!=ID_pointer)
  {
    error().source_location = expr.source_location();
    error() << "type cast to '" << to_string(expr_type) << "' is not permitted"
            << eom;
    throw 0;
  }

  if(is_numeric_type(op_type) || op_type.id()==ID_pointer)
  {
  }
  else if(op_type.id()==ID_array)
  {
    index_exprt index(op, from_integer(0, c_index_type()));
    op=address_of_exprt(index);
  }
  else if(op_type.id()==ID_empty)
  {
    if(expr_type.id()!=ID_empty)
    {
      error().source_location = expr.source_location();
      error() << "type cast from void only permitted to void, but got '"
              << to_string(expr.type()) << "'" << eom;
      throw 0;
    }
  }
  else if(op_type.id()==ID_vector)
  {
    const vector_typet &op_vector_type=
      to_vector_type(op_type);

    // gcc allows conversion of a vector of size 1 to
    // an integer/float of the same size
    if((expr_type.id()==ID_signedbv ||
        expr_type.id()==ID_unsignedbv) &&
       pointer_offset_bits(expr_type, *this)==
       pointer_offset_bits(op_vector_type, *this))
    {
    }
    else
    {
      error().source_location = expr.source_location();
      error() << "type cast from vector to '" << to_string(expr.type())
              << "' not permitted" << eom;
      throw 0;
    }
  }
  else
  {
    error().source_location = expr.source_location();
    error() << "type cast from '" << to_string(op_type) << "' not permitted"
            << eom;
    throw 0;
  }

  // The new thing is an lvalue if the previous one is
  // an lvalue and it's just a pointer type cast.
  // This isn't really standard conformant!
  // Note that gcc says "warning: target of assignment not really an lvalue;
  // this will be a hard error in the future", i.e., we
  // can hope that the code below will one day simply go away.

  // Current versions of gcc in fact refuse to do this! Yay!

  if(op.get_bool(ID_C_lvalue))
  {
    if(expr_type.id()==ID_pointer)
      expr.set(ID_C_lvalue, true);
  }
}

void c_typecheck_baset::make_index_type(exprt &expr)
{
  implicit_typecast(expr, c_index_type());
}

void c_typecheck_baset::typecheck_expr_index(exprt &expr)
{
  exprt &array_expr = to_binary_expr(expr).op0();
  exprt &index_expr = to_binary_expr(expr).op1();

  // we might have to swap them

  {
    const typet &array_type = array_expr.type();
    const typet &index_type = index_expr.type();

    if(
      array_type.id() != ID_array && array_type.id() != ID_pointer &&
      array_type.id() != ID_vector &&
      (index_type.id() == ID_array || index_type.id() == ID_pointer ||
       index_type.id() == ID_vector))
      std::swap(array_expr, index_expr);
  }

  make_index_type(index_expr);

  // array_expr is a reference to one of expr.operands(), when that vector is
  // swapped below the reference is no longer valid. final_array_type exists
  // beyond that point so can't be a reference
  const typet final_array_type = array_expr.type();

  if(final_array_type.id()==ID_array ||
     final_array_type.id()==ID_vector)
  {
    expr.type() = to_type_with_subtype(final_array_type).subtype();

    if(array_expr.get_bool(ID_C_lvalue))
      expr.set(ID_C_lvalue, true);

    if(final_array_type.get_bool(ID_C_constant))
      expr.type().set(ID_C_constant, true);
  }
  else if(final_array_type.id()==ID_pointer)
  {
    // p[i] is syntactic sugar for *(p+i)

    typecheck_arithmetic_pointer(to_binary_expr(expr).op0());
    exprt::operandst summands;
    std::swap(summands, expr.operands());
    expr.add_to_operands(plus_exprt(std::move(summands), array_expr.type()));
    expr.id(ID_dereference);
    expr.set(ID_C_lvalue, true);
    expr.type() = to_pointer_type(final_array_type).base_type();
  }
  else
  {
    error().source_location = expr.source_location();
    error() << "operator [] must take array/vector or pointer but got '"
            << to_string(array_expr.type()) << "'" << eom;
    throw 0;
  }
}

void c_typecheck_baset::adjust_float_rel(binary_relation_exprt &expr)
{
  // equality and disequality on float is not mathematical equality!
  if(expr.op0().type().id() == ID_floatbv)
  {
    if(expr.id()==ID_equal)
      expr.id(ID_ieee_float_equal);
    else if(expr.id()==ID_notequal)
      expr.id(ID_ieee_float_notequal);
  }
}

void c_typecheck_baset::typecheck_expr_rel(
  binary_relation_exprt &expr)
{
  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=op0.type();
  const typet o_type1=op1.type();

  if(o_type0.id() == ID_vector || o_type1.id() == ID_vector)
  {
    typecheck_expr_rel_vector(expr);
    return;
  }

  expr.type()=bool_typet();

  if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    if(follow(o_type0)==follow(o_type1))
    {
      if(o_type0.id() != ID_array)
      {
        adjust_float_rel(expr);
        return; // no promotion necessary
      }
    }
  }

  implicit_typecast_arithmetic(op0, op1);

  const typet &type0=op0.type();
  const typet &type1=op1.type();

  if(type0==type1)
  {
    if(is_number(type0))
    {
      adjust_float_rel(expr);
      return;
    }

    if(type0.id()==ID_pointer)
    {
      if(expr.id()==ID_equal || expr.id()==ID_notequal)
        return;

      if(expr.id()==ID_le || expr.id()==ID_lt ||
         expr.id()==ID_ge || expr.id()==ID_gt)
        return;
    }

    if(type0.id()==ID_string_constant)
    {
      if(expr.id()==ID_equal || expr.id()==ID_notequal)
        return;
    }
  }
  else
  {
    // pointer and zero
    if(type0.id()==ID_pointer &&
       simplify_expr(op1, *this).is_zero())
    {
      op1 = null_pointer_exprt{to_pointer_type(type0)};
      return;
    }

    if(type1.id()==ID_pointer &&
       simplify_expr(op0, *this).is_zero())
    {
      op0 = null_pointer_exprt{to_pointer_type(type1)};
      return;
    }

    // pointer and integer
    if(type0.id()==ID_pointer && is_number(type1))
    {
      op1 = typecast_exprt(op1, type0);
      return;
    }

    if(type1.id()==ID_pointer && is_number(type0))
    {
      op0 = typecast_exprt(op0, type1);
      return;
    }

    if(type0.id()==ID_pointer && type1.id()==ID_pointer)
    {
      op1 = typecast_exprt(op1, type0);
      return;
    }
  }

  error().source_location = expr.source_location();
  error() << "operator '" << expr.id() << "' not defined for types '"
          << to_string(o_type0) << "' and '" << to_string(o_type1) << "'"
          << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_rel_vector(binary_exprt &expr)
{
  const typet &o_type0 = as_const(expr).op0().type();
  const typet &o_type1 = as_const(expr).op1().type();

  if(o_type0.id() != ID_vector || o_type0 != o_type1)
  {
    error().source_location = expr.source_location();
    error() << "vector operator '" << expr.id() << "' not defined for types '"
            << to_string(o_type0) << "' and '" << to_string(o_type1) << "'"
            << eom;
    throw 0;
  }

  // Comparisons between vectors produce a vector of integers of the same width
  // with the same dimension.
  auto subtype_width =
    to_bitvector_type(to_vector_type(o_type0).element_type()).get_width();
  expr.type() =
    vector_typet{signedbv_typet{subtype_width}, to_vector_type(o_type0).size()};

  // Replace the id as the semantics of these are point-wise application (and
  // the result is not of bool type).
  if(expr.id() == ID_notequal)
    expr.id(ID_vector_notequal);
  else
    expr.id("vector-" + id2string(expr.id()));
}

void c_typecheck_baset::typecheck_expr_ptrmember(exprt &expr)
{
  auto &op = to_unary_expr(expr).op();
  const typet &op0_type = op.type();

  if(op0_type.id() == ID_array)
  {
    // a->f is the same as a[0].f
    exprt zero = from_integer(0, c_index_type());
    index_exprt index_expr(op, zero, to_array_type(op0_type).element_type());
    index_expr.set(ID_C_lvalue, true);
    op.swap(index_expr);
  }
  else if(op0_type.id() == ID_pointer)
  {
    // turn x->y into (*x).y
    dereference_exprt deref_expr(op);
    deref_expr.add_source_location()=expr.source_location();
    typecheck_expr_dereference(deref_expr);
    op.swap(deref_expr);
  }
  else
  {
    error().source_location = expr.source_location();
    error() << "ptrmember operator requires pointer or array type "
               "on left hand side, but got '"
            << to_string(op0_type) << "'" << eom;
    throw 0;
  }

  expr.id(ID_member);
  typecheck_expr_member(expr);
}

void c_typecheck_baset::typecheck_expr_member(exprt &expr)
{
  exprt &op0 = to_unary_expr(expr).op();
  typet type=op0.type();

  type = follow(type);

  if(type.id()!=ID_struct &&
     type.id()!=ID_union)
  {
    error().source_location = expr.source_location();
    error() << "member operator requires structure type "
               "on left hand side but got '"
            << to_string(type) << "'" << eom;
    throw 0;
  }

  const struct_union_typet &struct_union_type=
    to_struct_union_type(type);

  if(struct_union_type.is_incomplete())
  {
    error().source_location = expr.source_location();
    error() << "member operator got incomplete " << type.id()
            << " type on left hand side" << eom;
    throw 0;
  }

  const irep_idt &component_name=
    expr.get(ID_component_name);

  // first try to find directly
  const struct_union_typet::componentt &component =
    struct_union_type.get_component(component_name);

  // if that fails, search the anonymous members

  if(component.is_nil())
  {
    exprt tmp=get_component_rec(op0, component_name, *this);

    if(tmp.is_nil())
    {
      // give up
      error().source_location = expr.source_location();
      error() << "member '" << component_name << "' not found in '"
              << to_string(type) << "'" << eom;
      throw 0;
    }

    // done!
    expr.swap(tmp);
    return;
  }

  expr.type()=component.type();

  if(op0.get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);

  if(op0.type().get_bool(ID_C_constant) || type.get_bool(ID_C_constant))
    expr.type().set(ID_C_constant, true);

  // copy method identifier
  const irep_idt &identifier=component.get(ID_C_identifier);

  if(!identifier.empty())
    expr.set(ID_C_identifier, identifier);

  const irep_idt &access=component.get_access();

  if(access==ID_private)
  {
    error().source_location = expr.source_location();
    error() << "member '" << component_name << "' is " << access << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_expr_trinary(if_exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  assert(operands.size()==3);

  // copy (save) original types
  const typet o_type0=operands[0].type();
  const typet o_type1=operands[1].type();
  const typet o_type2=operands[2].type();

  implicit_typecast_bool(operands[0]);

  if(o_type1.id() == ID_empty || o_type2.id() == ID_empty)
  {
    operands[1] = typecast_exprt::conditional_cast(operands[1], void_type());
    operands[2] = typecast_exprt::conditional_cast(operands[2], void_type());
    expr.type() = void_type();
    return;
  }

  if(operands[1].type().id()==ID_pointer &&
     operands[2].type().id()!=ID_pointer)
    implicit_typecast(operands[2], operands[1].type());
  else if(operands[2].type().id()==ID_pointer &&
          operands[1].type().id()!=ID_pointer)
    implicit_typecast(operands[1], operands[2].type());

  if(operands[1].type().id()==ID_pointer &&
     operands[2].type().id()==ID_pointer &&
     operands[1].type()!=operands[2].type())
  {
    exprt tmp1=simplify_expr(operands[1], *this);
    exprt tmp2=simplify_expr(operands[2], *this);

    // is one of them void * AND null? Convert that to the other.
    // (at least that's how GCC behaves)
    if(
      operands[1].type().subtype().id() == ID_empty && tmp1.is_constant() &&
      is_null_pointer(to_constant_expr(tmp1)))
    {
      implicit_typecast(operands[1], operands[2].type());
    }
    else if(
      operands[2].type().subtype().id() == ID_empty && tmp2.is_constant() &&
      is_null_pointer(to_constant_expr(tmp2)))
    {
      implicit_typecast(operands[2], operands[1].type());
    }
    else if(operands[1].type().subtype().id()!=ID_code ||
            operands[2].type().subtype().id()!=ID_code)
    {
      // Make it void *.
      // gcc and clang issue a warning for this.
      expr.type() = pointer_type(void_type());
      implicit_typecast(operands[1], expr.type());
      implicit_typecast(operands[2], expr.type());
    }
    else
    {
      // maybe functions without parameter lists
      const code_typet &c_type1=to_code_type(operands[1].type().subtype());
      const code_typet &c_type2=to_code_type(operands[2].type().subtype());

      if(c_type1.return_type()==c_type2.return_type())
      {
        if(c_type1.parameters().empty() && c_type1.has_ellipsis())
          implicit_typecast(operands[1], operands[2].type());
        else if(c_type2.parameters().empty() && c_type2.has_ellipsis())
          implicit_typecast(operands[2], operands[1].type());
      }
    }
  }

  if(operands[1].type().id()==ID_empty ||
     operands[2].type().id()==ID_empty)
  {
    expr.type()=void_type();
    return;
  }

  if(
    operands[1].type() != operands[2].type() ||
    operands[1].type().id() == ID_array)
  {
    implicit_typecast_arithmetic(operands[1], operands[2]);
  }

  if(operands[1].type() == operands[2].type())
  {
    expr.type()=operands[1].type();

    // GCC says: "A conditional expression is a valid lvalue
    // if its type is not void and the true and false branches
    // are both valid lvalues."

    if(operands[1].get_bool(ID_C_lvalue) &&
       operands[2].get_bool(ID_C_lvalue))
      expr.set(ID_C_lvalue, true);

    return;
  }

  error().source_location = expr.source_location();
  error() << "operator ?: not defined for types '" << to_string(o_type1)
          << "' and '" << to_string(o_type2) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_side_effect_gcc_conditional_expression(
  side_effect_exprt &expr)
{
  // x ? : y is almost the same as x ? x : y,
  // but not quite, as x is evaluated only once

  exprt::operandst &operands=expr.operands();

  if(operands.size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "gcc conditional_expr expects two operands" << eom;
    throw 0;
  }

  // use typechecking code for "if"

  if_exprt if_expr(operands[0], operands[0], operands[1]);
  if_expr.add_source_location()=expr.source_location();

  typecheck_expr_trinary(if_expr);

  // copy the result
  operands[0] = if_expr.true_case();
  operands[1] = if_expr.false_case();
  expr.type()=if_expr.type();
}

void c_typecheck_baset::typecheck_expr_address_of(exprt &expr)
{
  exprt &op = to_unary_expr(expr).op();

  if(op.type().id()==ID_c_bit_field)
  {
    error().source_location = expr.source_location();
    error() << "cannot take address of a bit field" << eom;
    throw 0;
  }

  if(op.type().id() == ID_bool)
  {
    error().source_location = expr.source_location();
    error() << "cannot take address of a single bit" << eom;
    throw 0;
  }

  // special case: address of label
  if(op.id()==ID_label)
  {
    expr.type()=pointer_type(void_type());

    // remember the label
    labels_used[op.get(ID_identifier)]=op.source_location();
    return;
  }

  // special case: address of function designator
  // ANSI-C 99 section 6.3.2.1 paragraph 4

  if(
    op.id() == ID_address_of && op.get_bool(ID_C_implicit) &&
    to_address_of_expr(op).object().type().id() == ID_code)
  {
    // make the implicit address_of an explicit address_of
    exprt tmp;
    tmp.swap(op);
    tmp.set(ID_C_implicit, false);
    expr.swap(tmp);
    return;
  }

  if(op.id()==ID_struct ||
     op.id()==ID_union ||
     op.id()==ID_array ||
     op.id()==ID_string_constant)
  {
    // these are really objects
  }
  else if(op.get_bool(ID_C_lvalue))
  {
    // ok
  }
  else if(op.type().id()==ID_code)
  {
    // ok
  }
  else
  {
    error().source_location = expr.source_location();
    error() << "address_of error: '" << to_string(op) << "' not an lvalue"
            << eom;
    throw 0;
  }

  expr.type()=pointer_type(op.type());
}

void c_typecheck_baset::typecheck_expr_dereference(exprt &expr)
{
  exprt &op = to_unary_expr(expr).op();

  const typet op_type = op.type();

  if(op_type.id()==ID_array)
  {
    // *a is the same as a[0]
    expr.id(ID_index);
    expr.type() = to_array_type(op_type).element_type();
    expr.copy_to_operands(from_integer(0, c_index_type()));
    assert(expr.operands().size()==2);
  }
  else if(op_type.id()==ID_pointer)
  {
    expr.type() = to_pointer_type(op_type).base_type();

    if(
      expr.type().id() == ID_empty &&
      config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
    {
      error().source_location = expr.source_location();
      error() << "dereferencing void pointer" << eom;
      throw 0;
    }
  }
  else
  {
    error().source_location = expr.source_location();
    error() << "operand of unary * '" << to_string(op)
            << "' is not a pointer, but got '" << to_string(op_type) << "'"
            << eom;
    throw 0;
  }

  expr.set(ID_C_lvalue, true);

  // if you dereference a pointer pointing to
  // a function, you get a pointer again
  // allowing ******...*p

  typecheck_expr_function_identifier(expr);
}

void c_typecheck_baset::typecheck_expr_function_identifier(exprt &expr)
{
  if(expr.type().id()==ID_code)
  {
    address_of_exprt tmp(expr, pointer_type(expr.type()));
    tmp.set(ID_C_implicit, true);
    tmp.add_source_location()=expr.source_location();
    expr=tmp;
  }
}

void c_typecheck_baset::typecheck_expr_side_effect(side_effect_exprt &expr)
{
  const irep_idt &statement=expr.get_statement();

  if(statement==ID_preincrement ||
     statement==ID_predecrement ||
     statement==ID_postincrement ||
     statement==ID_postdecrement)
  {
    const exprt &op0 = to_unary_expr(expr).op();
    const typet &type0=op0.type();

    if(!op0.get_bool(ID_C_lvalue))
    {
      error().source_location = op0.source_location();
      error() << "prefix operator error: '" << to_string(op0)
              << "' not an lvalue" << eom;
      throw 0;
    }

    if(type0.get_bool(ID_C_constant))
    {
      error().source_location = op0.source_location();
      error() << "error: '" << to_string(op0) << "' is constant" << eom;
      throw 0;
    }

    if(type0.id() == ID_c_enum_tag)
    {
      const c_enum_typet &enum_type = follow_tag(to_c_enum_tag_type(type0));
      if(enum_type.is_incomplete())
      {
        error().source_location = expr.source_location();
        error() << "operator '" << statement << "' given incomplete type '"
                << to_string(type0) << "'" << eom;
        throw 0;
      }

      // increment/decrement on underlying type
      to_unary_expr(expr).op() =
        typecast_exprt(op0, enum_type.underlying_type());
      expr.type() = enum_type.underlying_type();
    }
    else if(type0.id() == ID_c_bit_field)
    {
      // promote to underlying type
      typet underlying_type = to_c_bit_field_type(type0).underlying_type();
      to_unary_expr(expr).op() = typecast_exprt(op0, underlying_type);
      expr.type()=underlying_type;
    }
    else if(type0.id() == ID_bool || type0.id() == ID_c_bool)
    {
      implicit_typecast_arithmetic(to_unary_expr(expr).op());
      expr.type() = op0.type();
    }
    else if(is_numeric_type(type0))
    {
      expr.type()=type0;
    }
    else if(type0.id() == ID_pointer)
    {
      expr.type()=type0;
      typecheck_arithmetic_pointer(op0);
    }
    else
    {
      error().source_location = expr.source_location();
      error() << "operator '" << statement << "' not defined for type '"
              << to_string(type0) << "'" << eom;
      throw 0;
    }
  }
  else if(has_prefix(id2string(statement), "assign"))
    typecheck_side_effect_assignment(expr);
  else if(statement==ID_function_call)
    typecheck_side_effect_function_call(
      to_side_effect_expr_function_call(expr));
  else if(statement==ID_statement_expression)
    typecheck_side_effect_statement_expression(expr);
  else if(statement==ID_gcc_conditional_expression)
    typecheck_side_effect_gcc_conditional_expression(expr);
  else
  {
    error().source_location = expr.source_location();
    error() << "unknown side effect: " << statement << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "function_call side effect expects two operands" << eom;
    throw 0;
  }

  exprt &f_op=expr.function();

  // f_op is not yet typechecked, in contrast to the other arguments.
  // This is a big special case!

  if(f_op.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(f_op).get_identifier();

    asm_label_mapt::const_iterator entry=
      asm_label_map.find(identifier);
    if(entry!=asm_label_map.end())
      identifier=entry->second;

    if(symbol_table.symbols.find(identifier)==symbol_table.symbols.end())
    {
      // This is an undeclared function.
      // Is this a builtin?
      if(!builtin_factory(identifier, symbol_table, get_message_handler()))
      {
        // yes, it's a builtin
      }
      else if(
        identifier == "__noop" &&
        config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
      {
        // https://docs.microsoft.com/en-us/cpp/intrinsics/noop
        // typecheck and discard, just generating 0 instead
        for(auto &op : expr.arguments())
          typecheck_expr(op);

        exprt result = from_integer(0, signed_int_type());
        expr.swap(result);

        return;
      }
      else if(
        identifier == "__builtin_shuffle" &&
        config.ansi_c.mode == configt::ansi_ct::flavourt::GCC)
      {
        exprt result = typecheck_shuffle_vector(expr);
        expr.swap(result);

        return;
      }
      else if(
        identifier == "__builtin_shufflevector" &&
        config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG)
      {
        exprt result = typecheck_shuffle_vector(expr);
        expr.swap(result);

        return;
      }
      else if(
        identifier == CPROVER_PREFIX "saturating_minus" ||
        identifier == CPROVER_PREFIX "saturating_plus")
      {
        exprt result = typecheck_saturating_arithmetic(expr);
        expr.swap(result);

        return;
      }
      else if(
        auto gcc_polymorphic = typecheck_gcc_polymorphic_builtin(
          identifier, expr.arguments(), f_op.source_location()))
      {
        irep_idt identifier_with_type = gcc_polymorphic->get_identifier();
        auto &parameters = to_code_type(gcc_polymorphic->type()).parameters();
        INVARIANT(
          !parameters.empty(),
          "GCC polymorphic built-ins should have at least one parameter");

        // For all atomic/sync polymorphic built-ins (which are the ones handled
        // by typecheck_gcc_polymorphic_builtin), looking at the first parameter
        // suffices to distinguish different implementations.
        if(parameters.front().type().id() == ID_pointer)
        {
          identifier_with_type = id2string(identifier) + "_" +
                                 type_to_partial_identifier(
                                   parameters.front().type().subtype(), *this);
        }
        else
        {
          identifier_with_type =
            id2string(identifier) + "_" +
            type_to_partial_identifier(parameters.front().type(), *this);
        }
        gcc_polymorphic->set_identifier(identifier_with_type);

        if(!symbol_table.has_symbol(identifier_with_type))
        {
          for(std::size_t i = 0; i < parameters.size(); ++i)
          {
            const std::string base_name = "p_" + std::to_string(i);

            parameter_symbolt new_symbol;

            new_symbol.name =
              id2string(identifier_with_type) + "::" + base_name;
            new_symbol.base_name = base_name;
            new_symbol.location = f_op.source_location();
            new_symbol.type = parameters[i].type();
            new_symbol.is_parameter = true;
            new_symbol.is_lvalue = true;
            new_symbol.mode = ID_C;

            parameters[i].set_identifier(new_symbol.name);
            parameters[i].set_base_name(new_symbol.base_name);

            symbol_table.add(new_symbol);
          }

          symbolt new_symbol;

          new_symbol.name = identifier_with_type;
          new_symbol.base_name = identifier_with_type;
          new_symbol.location = f_op.source_location();
          new_symbol.type = gcc_polymorphic->type();
          new_symbol.mode = ID_C;
          code_blockt implementation =
            instantiate_gcc_polymorphic_builtin(identifier, *gcc_polymorphic);
          typet parent_return_type = return_type;
          return_type = to_code_type(gcc_polymorphic->type()).return_type();
          typecheck_code(implementation);
          return_type = parent_return_type;
          new_symbol.value = implementation;

          symbol_table.add(new_symbol);
        }

        f_op = std::move(*gcc_polymorphic);
      }
      else
      {
        // This is an undeclared function that's not a builtin.
        // Let's just add it.
        // We do a bit of return-type guessing, but just a bit.
        typet guessed_return_type = signed_int_type();

        // The following isn't really right and sound, but there
        // are too many idiots out there who use malloc and the like
        // without the right header file.
        if(identifier=="malloc" ||
           identifier=="realloc" ||
           identifier=="reallocf" ||
           identifier=="valloc")
        {
          guessed_return_type = pointer_type(void_type()); // void *
        }

        symbolt new_symbol;

        new_symbol.name=identifier;
        new_symbol.base_name=identifier;
        new_symbol.location=expr.source_location();
        new_symbol.type = code_typet({}, guessed_return_type);
        new_symbol.type.set(ID_C_incomplete, true);

        // TODO: should also guess some argument types

        symbolt *symbol_ptr;
        move_symbol(new_symbol, symbol_ptr);

        warning().source_location=f_op.find_source_location();
        warning() << "function '" << identifier << "' is not declared" << eom;
      }
    }
  }

  // typecheck it now
  typecheck_expr(f_op);

  const typet f_op_type = f_op.type();

  if(f_op_type.id() == ID_mathematical_function)
  {
    const auto &mathematical_function_type =
      to_mathematical_function_type(f_op_type);

    // check number of arguments
    if(expr.arguments().size() != mathematical_function_type.domain().size())
    {
      error().source_location = f_op.source_location();
      error() << "expected " << mathematical_function_type.domain().size()
              << " arguments but got " << expr.arguments().size() << eom;
      throw 0;
    }

    // check the types of the arguments
    for(auto &p :
        make_range(expr.arguments()).zip(mathematical_function_type.domain()))
    {
      if(p.first.type() != p.second)
      {
        error().source_location = p.first.source_location();
        error() << "expected argument of type " << to_string(p.second)
                << " but got " << to_string(p.first.type()) << eom;
        throw 0;
      }
    }

    function_application_exprt function_application(f_op, expr.arguments());

    function_application.add_source_location() = expr.source_location();

    expr.swap(function_application);
    return;
  }

  if(f_op_type.id()!=ID_pointer)
  {
    error().source_location = f_op.source_location();
    error() << "expected function/function pointer as argument but got '"
            << to_string(f_op_type) << "'" << eom;
    throw 0;
  }

  // do implicit dereference
  if(f_op.id() == ID_address_of && f_op.get_bool(ID_C_implicit))
  {
    f_op = to_address_of_expr(f_op).object();
  }
  else
  {
    dereference_exprt tmp{f_op};
    tmp.set(ID_C_implicit, true);
    tmp.add_source_location()=f_op.source_location();
    f_op.swap(tmp);
  }

  if(f_op.type().id()!=ID_code)
  {
    error().source_location = f_op.source_location();
    error() << "expected code as argument" << eom;
    throw 0;
  }

  const code_typet &code_type=to_code_type(f_op.type());

  expr.type()=code_type.return_type();

  exprt tmp=do_special_functions(expr);

  if(tmp.is_not_nil())
    expr.swap(tmp);
  else
    typecheck_function_call_arguments(expr);
}

exprt c_typecheck_baset::do_special_functions(
  side_effect_expr_function_callt &expr)
{
  const exprt &f_op=expr.function();
  const source_locationt &source_location=expr.source_location();

  // some built-in functions
  if(f_op.id()!=ID_symbol)
    return nil_exprt();

  const irep_idt &identifier=to_symbol_expr(f_op).get_identifier();

  if(identifier == CPROVER_PREFIX "is_fresh")
  {
    if(expr.arguments().size() != 2)
    {
      error().source_location = f_op.source_location();
      error() << CPROVER_PREFIX "is_fresh expects two operands; "
              << expr.arguments().size() << "provided." << eom;
      throw 0;
    }
    typecheck_function_call_arguments(expr);
    return nil_exprt();
  }
  else if(identifier == CPROVER_PREFIX "same_object")
  {
    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "same_object expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt same_object_expr=
      same_object(expr.arguments()[0], expr.arguments()[1]);
    same_object_expr.add_source_location()=source_location;

    return same_object_expr;
  }
  else if(identifier==CPROVER_PREFIX "get_must")
  {
    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "get_must expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    binary_predicate_exprt get_must_expr(
      expr.arguments()[0], ID_get_must, expr.arguments()[1]);
    get_must_expr.add_source_location()=source_location;

    return std::move(get_must_expr);
  }
  else if(identifier==CPROVER_PREFIX "get_may")
  {
    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "get_may expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    binary_predicate_exprt get_may_expr(
      expr.arguments()[0], ID_get_may, expr.arguments()[1]);
    get_may_expr.add_source_location()=source_location;

    return std::move(get_may_expr);
  }
  else if(identifier == CPROVER_PREFIX "is_invalid_pointer")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "is_invalid_pointer expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt same_object_expr = is_invalid_pointer_exprt{expr.arguments().front()};
    same_object_expr.add_source_location()=source_location;

    return same_object_expr;
  }
  else if(identifier==CPROVER_PREFIX "buffer_size")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "buffer_size expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt buffer_size_expr("buffer_size", size_type());
    buffer_size_expr.operands()=expr.arguments();
    buffer_size_expr.add_source_location()=source_location;

    return buffer_size_expr;
  }
  else if(identifier==CPROVER_PREFIX "is_zero_string")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "is_zero_string expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    unary_exprt is_zero_string_expr(
      "is_zero_string", expr.arguments()[0], c_bool_type());
    is_zero_string_expr.set(ID_C_lvalue, true); // make it an lvalue
    is_zero_string_expr.add_source_location()=source_location;

    return std::move(is_zero_string_expr);
  }
  else if(identifier==CPROVER_PREFIX "zero_string_length")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "zero_string_length expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt zero_string_length_expr("zero_string_length", size_type());
    zero_string_length_expr.operands()=expr.arguments();
    zero_string_length_expr.set(ID_C_lvalue, true); // make it an lvalue
    zero_string_length_expr.add_source_location()=source_location;

    return zero_string_length_expr;
  }
  else if(identifier==CPROVER_PREFIX "DYNAMIC_OBJECT")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "dynamic_object expects one argument" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt is_dynamic_object_expr = is_dynamic_object_exprt(expr.arguments()[0]);
    is_dynamic_object_expr.add_source_location() = source_location;

    return is_dynamic_object_expr;
  }
  else if(identifier==CPROVER_PREFIX "POINTER_OFFSET")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "pointer_offset expects one argument" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt pointer_offset_expr=pointer_offset(expr.arguments().front());
    pointer_offset_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(pointer_offset_expr, expr.type());
  }
  else if(identifier == CPROVER_PREFIX "OBJECT_SIZE")
  {
    if(expr.arguments().size() != 1)
    {
      error().source_location = f_op.source_location();
      error() << "object_size expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    object_size_exprt object_size_expr(expr.arguments()[0], size_type());
    object_size_expr.add_source_location() = source_location;

    return std::move(object_size_expr);
  }
  else if(identifier==CPROVER_PREFIX "POINTER_OBJECT")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "pointer_object expects one argument" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt pointer_object_expr = pointer_object(expr.arguments().front());
    pointer_object_expr.add_source_location() = source_location;

    return typecast_exprt::conditional_cast(pointer_object_expr, expr.type());
  }
  else if(identifier=="__builtin_bswap16" ||
          identifier=="__builtin_bswap32" ||
          identifier=="__builtin_bswap64")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // these are hard-wired to 8 bits according to the gcc manual
    bswap_exprt bswap_expr(expr.arguments().front(), 8, expr.type());
    bswap_expr.add_source_location()=source_location;

    return std::move(bswap_expr);
  }
  else if(
    identifier == "__builtin_rotateleft8" ||
    identifier == "__builtin_rotateleft16" ||
    identifier == "__builtin_rotateleft32" ||
    identifier == "__builtin_rotateleft64" ||
    identifier == "__builtin_rotateright8" ||
    identifier == "__builtin_rotateright16" ||
    identifier == "__builtin_rotateright32" ||
    identifier == "__builtin_rotateright64")
  {
    // clang only
    if(expr.arguments().size() != 2)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    irep_idt id = (identifier == "__builtin_rotateleft8" ||
                   identifier == "__builtin_rotateleft16" ||
                   identifier == "__builtin_rotateleft32" ||
                   identifier == "__builtin_rotateleft64")
                    ? ID_rol
                    : ID_ror;

    shift_exprt rotate_expr(expr.arguments()[0], id, expr.arguments()[1]);
    rotate_expr.add_source_location() = source_location;

    return std::move(rotate_expr);
  }
  else if(identifier=="__builtin_nontemporal_load")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // these return the subtype of the argument
    exprt &ptr_arg=expr.arguments().front();

    if(ptr_arg.type().id()!=ID_pointer)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_nontemporal_load takes pointer as argument" << eom;
      throw 0;
    }

    expr.type()=expr.arguments().front().type().subtype();

    return expr;
  }
  else if(
    identifier == "__builtin_fpclassify" ||
    identifier == CPROVER_PREFIX "fpclassify")
  {
    if(expr.arguments().size() != 6)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects six arguments" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // This gets 5 integers followed by a float or double.
    // The five integers are the return values for the cases
    // FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL and FP_ZERO.
    // gcc expects this to be able to produce compile-time constants.

    const exprt &fp_value = expr.arguments()[5];

    if(fp_value.type().id() != ID_floatbv)
    {
      error().source_location = fp_value.source_location();
      error() << "non-floating-point argument for " << identifier << eom;
      throw 0;
    }

    const auto &floatbv_type = to_floatbv_type(fp_value.type());

    const exprt zero = ieee_floatt::zero(floatbv_type).to_expr();

    const auto &arguments = expr.arguments();

    return if_exprt(
      isnan_exprt(fp_value),
      arguments[0],
      if_exprt(
        isinf_exprt(fp_value),
        arguments[1],
        if_exprt(
          isnormal_exprt(fp_value),
          arguments[2],
          if_exprt(
            ieee_float_equal_exprt(fp_value, zero),
            arguments[4],
            arguments[3])))); // subnormal
  }
  else if(identifier==CPROVER_PREFIX "isnanf" ||
          identifier==CPROVER_PREFIX "isnand" ||
          identifier==CPROVER_PREFIX "isnanld" ||
          identifier=="__builtin_isnan")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "isnan expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    isnan_exprt isnan_expr(expr.arguments().front());
    isnan_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(isnan_expr, expr.type());
  }
  else if(identifier==CPROVER_PREFIX "isfinitef" ||
          identifier==CPROVER_PREFIX "isfinited" ||
          identifier==CPROVER_PREFIX "isfiniteld")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "isfinite expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    isfinite_exprt isfinite_expr(expr.arguments().front());
    isfinite_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(isfinite_expr, expr.type());
  }
  else if(identifier==CPROVER_PREFIX "inf" ||
          identifier=="__builtin_inf")
  {
    constant_exprt inf_expr=
      ieee_floatt::plus_infinity(
        ieee_float_spect::double_precision()).to_expr();
    inf_expr.add_source_location()=source_location;

    return std::move(inf_expr);
  }
  else if(identifier==CPROVER_PREFIX "inff")
  {
    constant_exprt inff_expr=
      ieee_floatt::plus_infinity(
        ieee_float_spect::single_precision()).to_expr();
    inff_expr.add_source_location()=source_location;

    return std::move(inff_expr);
  }
  else if(identifier==CPROVER_PREFIX "infl")
  {
    floatbv_typet type=to_floatbv_type(long_double_type());
    constant_exprt infl_expr=
      ieee_floatt::plus_infinity(ieee_float_spect(type)).to_expr();
    infl_expr.add_source_location()=source_location;

    return std::move(infl_expr);
  }
  else if(identifier==CPROVER_PREFIX "abs" ||
          identifier==CPROVER_PREFIX "labs" ||
          identifier==CPROVER_PREFIX "llabs" ||
          identifier==CPROVER_PREFIX "fabs" ||
          identifier==CPROVER_PREFIX "fabsf" ||
          identifier==CPROVER_PREFIX "fabsl")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "abs-functions expect one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    abs_exprt abs_expr(expr.arguments().front());
    abs_expr.add_source_location()=source_location;

    return std::move(abs_expr);
  }
  else if(
    identifier == CPROVER_PREFIX "fmod" ||
    identifier == CPROVER_PREFIX "fmodf" ||
    identifier == CPROVER_PREFIX "fmodl")
  {
    if(expr.arguments().size() != 2)
    {
      error().source_location = f_op.source_location();
      error() << "fmod-functions expect two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // Note that the semantics differ from the
    // "floating point remainder" operation as defined by IEEE.
    // Note that these do not take a rounding mode.
    binary_exprt fmod_expr(
      expr.arguments()[0], ID_floatbv_mod, expr.arguments()[1]);

    fmod_expr.add_source_location() = source_location;

    return std::move(fmod_expr);
  }
  else if(
    identifier == CPROVER_PREFIX "remainder" ||
    identifier == CPROVER_PREFIX "remainderf" ||
    identifier == CPROVER_PREFIX "remainderl")
  {
    if(expr.arguments().size() != 2)
    {
      error().source_location = f_op.source_location();
      error() << "remainder-functions expect two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // The semantics of these functions is meant to match the
    // "floating point remainder" operation as defined by IEEE.
    // Note that these do not take a rounding mode.
    binary_exprt floatbv_rem_expr(
      expr.arguments()[0], ID_floatbv_rem, expr.arguments()[1]);

    floatbv_rem_expr.add_source_location() = source_location;

    return std::move(floatbv_rem_expr);
  }
  else if(identifier==CPROVER_PREFIX "allocate")
  {
    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "allocate expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    side_effect_exprt malloc_expr(ID_allocate, expr.type(), source_location);
    malloc_expr.operands()=expr.arguments();

    return std::move(malloc_expr);
  }
  else if(
    identifier == CPROVER_PREFIX "r_ok" ||
    identifier == CPROVER_PREFIX "w_ok" || identifier == CPROVER_PREFIX "rw_ok")
  {
    if(expr.arguments().size() != 1 && expr.arguments().size() != 2)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one or two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // the first argument must be a pointer
    const auto &pointer_expr = expr.arguments()[0];
    if(pointer_expr.type().id() != ID_pointer)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects a pointer as first argument" << eom;
      throw 0;
    }

    // The second argument, when given, is a size_t.
    // When not given, use the pointer subtype.
    exprt size_expr;

    if(expr.arguments().size() == 2)
    {
      implicit_typecast(expr.arguments()[1], size_type());
      size_expr = expr.arguments()[1];
    }
    else
    {
      // Won't do void *
      const auto &subtype = to_pointer_type(pointer_expr.type()).base_type();
      if(subtype.id() == ID_empty)
      {
        error().source_location = f_op.source_location();
        error() << identifier << " expects a size when given a void pointer"
                << eom;
        throw 0;
      }

      auto size_expr_opt = size_of_expr(subtype, *this);
      if(!size_expr_opt.has_value())
      {
        error().source_location = f_op.source_location();
        error() << identifier << " was given object pointer without size"
                << eom;
        throw 0;
      }

      size_expr = std::move(size_expr_opt.value());
    }

    irep_idt id = identifier == CPROVER_PREFIX "r_ok"
                    ? ID_r_ok
                    : identifier == CPROVER_PREFIX "w_ok" ? ID_w_ok : ID_rw_ok;

    r_or_w_ok_exprt ok_expr(id, pointer_expr, size_expr);
    ok_expr.add_source_location() = source_location;

    return std::move(ok_expr);
  }
  else if(
    (identifier == CPROVER_PREFIX "old") ||
    (identifier == CPROVER_PREFIX "loop_entry"))
  {
    if(expr.arguments().size() != 1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    irep_idt id = identifier == CPROVER_PREFIX "old" ? ID_old : ID_loop_entry;

    history_exprt old_expr(expr.arguments()[0], id);
    old_expr.add_source_location() = source_location;

    return std::move(old_expr);
  }
  else if(identifier==CPROVER_PREFIX "isinff" ||
          identifier==CPROVER_PREFIX "isinfd" ||
          identifier==CPROVER_PREFIX "isinfld" ||
          identifier=="__builtin_isinf")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    const exprt &fp_value = expr.arguments().front();

    if(fp_value.type().id() != ID_floatbv)
    {
      error().source_location = fp_value.source_location();
      error() << "non-floating-point argument for " << identifier << eom;
      throw 0;
    }

    isinf_exprt isinf_expr(expr.arguments().front());
    isinf_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(isinf_expr, expr.type());
  }
  else if(identifier == "__builtin_isinf_sign")
  {
    if(expr.arguments().size() != 1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    // returns 1 for +inf and -1 for -inf, and 0 otherwise

    const exprt &fp_value = expr.arguments().front();

    if(fp_value.type().id() != ID_floatbv)
    {
      error().source_location = fp_value.source_location();
      error() << "non-floating-point argument for " << identifier << eom;
      throw 0;
    }

    isinf_exprt isinf_expr(fp_value);
    isinf_expr.add_source_location() = source_location;

    return if_exprt(
      isinf_exprt(fp_value),
      if_exprt(
        sign_exprt(fp_value),
        from_integer(-1, expr.type()),
        from_integer(1, expr.type())),
      from_integer(0, expr.type()));
  }
  else if(identifier == CPROVER_PREFIX "isnormalf" ||
          identifier == CPROVER_PREFIX "isnormald" ||
          identifier == CPROVER_PREFIX "isnormalld" ||
          identifier == "__builtin_isnormal")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    const exprt &fp_value = expr.arguments()[0];

    if(fp_value.type().id() != ID_floatbv)
    {
      error().source_location = fp_value.source_location();
      error() << "non-floating-point argument for " << identifier << eom;
      throw 0;
    }

    isnormal_exprt isnormal_expr(expr.arguments().front());
    isnormal_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(isnormal_expr, expr.type());
  }
  else if(identifier==CPROVER_PREFIX "signf" ||
          identifier==CPROVER_PREFIX "signd" ||
          identifier==CPROVER_PREFIX "signld" ||
          identifier=="__builtin_signbit" ||
          identifier=="__builtin_signbitf" ||
          identifier=="__builtin_signbitl")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    sign_exprt sign_expr(expr.arguments().front());
    sign_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(sign_expr, expr.type());
  }
  else if(identifier=="__builtin_popcount" ||
          identifier=="__builtin_popcountl" ||
          identifier=="__builtin_popcountll" ||
          identifier=="__popcnt16" ||
          identifier=="__popcnt" ||
          identifier=="__popcnt64")
  {
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    popcount_exprt popcount_expr(expr.arguments().front(), expr.type());
    popcount_expr.add_source_location()=source_location;

    return std::move(popcount_expr);
  }
  else if(
    identifier == "__builtin_clz" || identifier == "__builtin_clzl" ||
    identifier == "__builtin_clzll" || identifier == "__lzcnt16" ||
    identifier == "__lzcnt" || identifier == "__lzcnt64")
  {
    if(expr.arguments().size() != 1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    count_leading_zeros_exprt clz{expr.arguments().front(),
                                  has_prefix(id2string(identifier), "__lzcnt"),
                                  expr.type()};
    clz.add_source_location() = source_location;

    return std::move(clz);
  }
  else if(
    identifier == "__builtin_ctz" || identifier == "__builtin_ctzl" ||
    identifier == "__builtin_ctzll")
  {
    if(expr.arguments().size() != 1)
    {
      error().source_location = f_op.source_location();
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    count_trailing_zeros_exprt ctz{
      expr.arguments().front(), false, expr.type()};
    ctz.add_source_location() = source_location;

    return std::move(ctz);
  }
  else if(identifier==CPROVER_PREFIX "equal")
  {
    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "equal expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    equal_exprt equality_expr(
      expr.arguments().front(), expr.arguments().back());
    equality_expr.add_source_location()=source_location;

    if(equality_expr.lhs().type() != equality_expr.rhs().type())
    {
      error().source_location = f_op.source_location();
      error() << "equal expects two operands of same type" << eom;
      throw 0;
    }

    return std::move(equality_expr);
  }
  else if(identifier=="__builtin_expect")
  {
    // This is a gcc extension to provide branch prediction.
    // We compile it away, but adding some IR instruction for
    // this would clearly be an option. Note that the type
    // of the return value is wired to "long", i.e.,
    // this may trigger a type conversion due to the signature
    // of this function.
    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_expect expects two arguments" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    return typecast_exprt(expr.arguments()[0], expr.type());
  }
  else if(identifier=="__builtin_object_size")
  {
    // this is a gcc extension to provide information about
    // object sizes at compile time
    // http://gcc.gnu.org/onlinedocs/gcc/Object-Size-Checking.html

    if(expr.arguments().size()!=2)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_object_size expects two arguments" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    make_constant(expr.arguments()[1]);

    mp_integer arg1;

    if(expr.arguments()[1].is_true())
      arg1=1;
    else if(expr.arguments()[1].is_false())
      arg1=0;
    else if(to_integer(to_constant_expr(expr.arguments()[1]), arg1))
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_object_size expects constant as second argument, "
              << "but got " << to_string(expr.arguments()[1]) << eom;
      throw 0;
    }

    exprt tmp;

    // the following means "don't know"
    if(arg1==0 || arg1==1)
    {
      tmp=from_integer(-1, size_type());
      tmp.add_source_location()=f_op.source_location();
    }
    else
    {
      tmp=from_integer(0, size_type());
      tmp.add_source_location()=f_op.source_location();
    }

    return tmp;
  }
  else if(identifier=="__builtin_choose_expr")
  {
    // this is a gcc extension similar to ?:
    if(expr.arguments().size()!=3)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_choose_expr expects three arguments" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt arg0 =
      typecast_exprt::conditional_cast(expr.arguments()[0], bool_typet());
    make_constant(arg0);

    if(arg0.is_true())
      return expr.arguments()[1];
    else
      return expr.arguments()[2];
  }
  else if(identifier=="__builtin_constant_p")
  {
    // this is a gcc extension to tell whether the argument
    // is known to be a compile-time constant
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_constant_p expects one argument" << eom;
      throw 0;
    }

    // do not typecheck the argument - it is never evaluated, and thus side
    // effects must not show up either

    // try to produce constant
    exprt tmp1=expr.arguments().front();
    simplify(tmp1, *this);

    bool is_constant=false;

    // Need to do some special treatment for string literals,
    // which are (void *)&("lit"[0])
    if(
      tmp1.id() == ID_typecast &&
      to_typecast_expr(tmp1).op().id() == ID_address_of &&
      to_address_of_expr(to_typecast_expr(tmp1).op()).object().id() ==
        ID_index &&
      to_index_expr(to_address_of_expr(to_typecast_expr(tmp1).op()).object())
          .array()
          .id() == ID_string_constant)
    {
      is_constant=true;
    }
    else
      is_constant=tmp1.is_constant();

    exprt tmp2=from_integer(is_constant, expr.type());
    tmp2.add_source_location()=source_location;

    return tmp2;
  }
  else if(identifier=="__builtin_classify_type")
  {
    // This is a gcc/clang extension that produces an integer
    // constant for the type of the argument expression.
    if(expr.arguments().size()!=1)
    {
      error().source_location = f_op.source_location();
      error() << "__builtin_classify_type expects one argument" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    exprt object=expr.arguments()[0];

    // The value doesn't matter at all, we only care about the type.
    // Need to sync with typeclass.h.
    typet type = follow(object.type());

    // use underlying type for bit fields
    if(type.id() == ID_c_bit_field)
      type = to_c_bit_field_type(type).underlying_type();

    unsigned type_number;

    if(type.id() == ID_bool || type.id() == ID_c_bool)
    {
      // clang returns 4 for _Bool, gcc treats these as 'int'.
      type_number =
        config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ? 4u : 1u;
    }
    else
    {
      type_number =
          type.id() == ID_empty
          ? 0u
          : (type.id() == ID_bool || type.id() == ID_c_bool)
            ? 4u
            : (type.id() == ID_pointer || type.id() == ID_array)
              ? 5u
              : type.id() == ID_floatbv
                ? 8u
                : (type.id() == ID_complex && type.subtype().id() == ID_floatbv)
                  ? 9u
                  : type.id() == ID_struct
                    ? 12u
                    : type.id() == ID_union
                      ? 13u
                      : 1u; // int, short, char, enum_tag
    }

    exprt tmp=from_integer(type_number, expr.type());
    tmp.add_source_location()=source_location;

    return tmp;
  }
  else if(
    identifier == CPROVER_PREFIX "overflow_minus" ||
    identifier == CPROVER_PREFIX "overflow_mult" ||
    identifier == CPROVER_PREFIX "overflow_plus" ||
    identifier == CPROVER_PREFIX "overflow_shl")
  {
    exprt overflow{identifier, typet{}, exprt::operandst{expr.arguments()}};
    overflow.add_source_location() = f_op.source_location();

    if(identifier == CPROVER_PREFIX "overflow_minus")
    {
      overflow.id(ID_minus);
      typecheck_expr_binary_arithmetic(overflow);
    }
    else if(identifier == CPROVER_PREFIX "overflow_mult")
    {
      overflow.id(ID_mult);
      typecheck_expr_binary_arithmetic(overflow);
    }
    else if(identifier == CPROVER_PREFIX "overflow_plus")
    {
      overflow.id(ID_plus);
      typecheck_expr_binary_arithmetic(overflow);
    }
    else if(identifier == CPROVER_PREFIX "overflow_shl")
    {
      overflow.id(ID_shl);
      typecheck_expr_shifts(to_shift_expr(overflow));
    }

    binary_overflow_exprt of{
      overflow.operands()[0], overflow.id(), overflow.operands()[1]};
    of.add_source_location() = overflow.source_location();
    return std::move(of);
  }
  else if(identifier == CPROVER_PREFIX "overflow_unary_minus")
  {
    exprt tmp{ID_unary_minus, typet{}, exprt::operandst{expr.arguments()}};
    tmp.add_source_location() = f_op.source_location();

    typecheck_expr_unary_arithmetic(tmp);

    unary_minus_overflow_exprt overflow{tmp.operands().front()};
    overflow.add_source_location() = tmp.source_location();
    return std::move(overflow);
  }
  else if(identifier == CPROVER_PREFIX "enum_is_in_range")
  {
    // Check correct number of arguments
    if(expr.arguments().size() != 1)
    {
      std::ostringstream error_message;
      error_message << expr.source_location().as_string() << ": " << identifier
                    << " takes exactly 1 argument, but "
                    << expr.arguments().size() << " were provided";
      throw invalid_source_file_exceptiont{error_message.str()};
    }
    auto arg1 = expr.arguments()[0];
    typecheck_expr(arg1);
    if(!can_cast_type<c_enum_tag_typet>(arg1.type()))
    {
      // Can't enum range check a non-enum
      std::ostringstream error_message;
      error_message << expr.source_location().as_string() << ": " << identifier
                    << " expects enum, but (" << expr2c(arg1, *this)
                    << ") has type `" << type2c(arg1.type(), *this) << '`';
      throw invalid_source_file_exceptiont{error_message.str()};
    }
    else
    {
      return expr;
    }
  }
  else if(
    identifier == "__builtin_add_overflow" ||
    identifier == "__builtin_sadd_overflow" ||
    identifier == "__builtin_saddl_overflow" ||
    identifier == "__builtin_saddll_overflow" ||
    identifier == "__builtin_uadd_overflow" ||
    identifier == "__builtin_uaddl_overflow" ||
    identifier == "__builtin_uaddll_overflow" ||
    identifier == "__builtin_add_overflow_p")
  {
    return typecheck_builtin_overflow(expr, ID_plus);
  }
  else if(
    identifier == "__builtin_sub_overflow" ||
    identifier == "__builtin_ssub_overflow" ||
    identifier == "__builtin_ssubl_overflow" ||
    identifier == "__builtin_ssubll_overflow" ||
    identifier == "__builtin_usub_overflow" ||
    identifier == "__builtin_usubl_overflow" ||
    identifier == "__builtin_usubll_overflow" ||
    identifier == "__builtin_sub_overflow_p")
  {
    return typecheck_builtin_overflow(expr, ID_minus);
  }
  else if(
    identifier == "__builtin_mul_overflow" ||
    identifier == "__builtin_smul_overflow" ||
    identifier == "__builtin_smull_overflow" ||
    identifier == "__builtin_smulll_overflow" ||
    identifier == "__builtin_umul_overflow" ||
    identifier == "__builtin_umull_overflow" ||
    identifier == "__builtin_umulll_overflow" ||
    identifier == "__builtin_mul_overflow_p")
  {
    return typecheck_builtin_overflow(expr, ID_mult);
  }
  else if(
    identifier == "__builtin_bitreverse8" ||
    identifier == "__builtin_bitreverse16" ||
    identifier == "__builtin_bitreverse32" ||
    identifier == "__builtin_bitreverse64")
  {
    // clang only
    if(expr.arguments().size() != 1)
    {
      std::ostringstream error_message;
      error_message << expr.source_location().as_string()
                    << ": error: " << identifier << " expects one operand";
      throw invalid_source_file_exceptiont{error_message.str()};
    }

    typecheck_function_call_arguments(expr);

    bitreverse_exprt bitreverse{expr.arguments()[0]};
    bitreverse.add_source_location() = source_location;

    return std::move(bitreverse);
  }
  else
    return nil_exprt();
  // NOLINTNEXTLINE(readability/fn_size)
}

exprt c_typecheck_baset::typecheck_builtin_overflow(
  side_effect_expr_function_callt &expr,
  const irep_idt &arith_op)
{
  const irep_idt &identifier = to_symbol_expr(expr.function()).get_identifier();

  // check function signature
  if(expr.arguments().size() != 3)
  {
    std::ostringstream error_message;
    error_message << expr.source_location().as_string() << ": " << identifier
                  << " takes exactly 3 arguments, but "
                  << expr.arguments().size() << " were provided";
    throw invalid_source_file_exceptiont{error_message.str()};
  }

  typecheck_function_call_arguments(expr);

  auto lhs = expr.arguments()[0];
  auto rhs = expr.arguments()[1];
  auto result = expr.arguments()[2];

  const bool is__p_variant = has_suffix(id2string(identifier), "_p");

  {
    auto const raise_wrong_argument_error =
      [this, identifier](
        const exprt &wrong_argument, std::size_t argument_number, bool _p) {
        std::ostringstream error_message;
        error_message << wrong_argument.source_location().as_string() << ": "
                      << identifier << " has signature " << identifier
                      << "(integral, integral, integral" << (_p ? "" : "*")
                      << "), "
                      << "but argument " << argument_number << " ("
                      << expr2c(wrong_argument, *this) << ") has type `"
                      << type2c(wrong_argument.type(), *this) << '`';
        throw invalid_source_file_exceptiont{error_message.str()};
      };
    for(int arg_index = 0; arg_index <= (!is__p_variant ? 1 : 2); ++arg_index)
    {
      auto const &argument = expr.arguments()[arg_index];

      if(!is_signed_or_unsigned_bitvector(argument.type()))
      {
        raise_wrong_argument_error(argument, arg_index + 1, is__p_variant);
      }
    }
    if(
      !is__p_variant &&
      (result.type().id() != ID_pointer ||
       !is_signed_or_unsigned_bitvector(result.type().subtype())))
    {
      raise_wrong_argument_error(result, 3, is__p_variant);
    }
  }

  return side_effect_expr_overflowt{arith_op,
                                    std::move(lhs),
                                    std::move(rhs),
                                    std::move(result),
                                    expr.source_location()};
}

exprt c_typecheck_baset::typecheck_saturating_arithmetic(
  const side_effect_expr_function_callt &expr)
{
  const irep_idt &identifier = to_symbol_expr(expr.function()).get_identifier();

  // check function signature
  if(expr.arguments().size() != 2)
  {
    std::ostringstream error_message;
    error_message << expr.source_location().as_string() << ": " << identifier
                  << " takes exactly two arguments, but "
                  << expr.arguments().size() << " were provided";
    throw invalid_source_file_exceptiont{error_message.str()};
  }

  exprt result;
  if(identifier == CPROVER_PREFIX "saturating_minus")
    result = saturating_minus_exprt{expr.arguments()[0], expr.arguments()[1]};
  else if(identifier == CPROVER_PREFIX "saturating_plus")
    result = saturating_plus_exprt{expr.arguments()[0], expr.arguments()[1]};
  else
    UNREACHABLE;

  typecheck_expr_binary_arithmetic(result);
  result.add_source_location() = expr.source_location();

  return result;
}

/// Typecheck the parameters in a function call expression, and where
/// necessary, make implicit casts around parameters explicit.
void c_typecheck_baset::typecheck_function_call_arguments(
  side_effect_expr_function_callt &expr)
{
  const exprt &f_op=expr.function();
  const code_typet &code_type=to_code_type(f_op.type());
  exprt::operandst &arguments=expr.arguments();
  const code_typet::parameterst &parameter_types=
    code_type.parameters();

  // no. of arguments test

  if(code_type.get_bool(ID_C_incomplete))
  {
    // can't check
  }
  else if(code_type.is_KnR())
  {
    // We are generous on KnR; any number is ok.
    // We will in missing ones with "NIL".

    while(parameter_types.size()>arguments.size())
      arguments.push_back(nil_exprt());
  }
  else if(code_type.has_ellipsis())
  {
    if(parameter_types.size()>arguments.size())
    {
      error().source_location = expr.source_location();
      error() << "not enough function arguments" << eom;
      throw 0;
    }
  }
  else if(parameter_types.size()!=arguments.size())
  {
    error().source_location = expr.source_location();
    error() << "wrong number of function arguments: "
            << "expected " << parameter_types.size()
            << ", but got " << arguments.size() << eom;
    throw 0;
  }

  for(std::size_t i=0; i<arguments.size(); i++)
  {
    exprt &op=arguments[i];

    if(op.is_nil())
    {
      // ignore
    }
    else if(i<parameter_types.size())
    {
      const code_typet::parametert &parameter_type=
        parameter_types[i];

      const typet &op_type=parameter_type.type();

      if(op_type.id()==ID_bool &&
         op.id()==ID_side_effect &&
         op.get(ID_statement)==ID_assign &&
         op.type().id()!=ID_bool)
      {
        warning().source_location=expr.find_source_location();
        warning() << "assignment where Boolean argument is expected" << eom;
      }

      implicit_typecast(op, op_type);
    }
    else
    {
      // don't know type, just do standard conversion

      if(op.type().id() == ID_array)
      {
        typet dest_type=pointer_type(void_type());
        dest_type.subtype().set(ID_C_constant, true);
        implicit_typecast(op, dest_type);
      }
    }
  }
}

void c_typecheck_baset::typecheck_expr_constant(exprt &)
{
  // nothing to do
}

void c_typecheck_baset::typecheck_expr_unary_arithmetic(exprt &expr)
{
  exprt &operand = to_unary_expr(expr).op();

  const typet &o_type = operand.type();

  if(o_type.id()==ID_vector)
  {
    if(is_number(to_vector_type(o_type).element_type()))
    {
      // Vector arithmetic.
      expr.type()=operand.type();
      return;
    }
  }

  implicit_typecast_arithmetic(operand);

  if(is_number(operand.type()))
  {
    expr.type()=operand.type();
    return;
  }

  error().source_location = expr.source_location();
  error() << "operator '" << expr.id() << "' not defined for type '"
          << to_string(operand.type()) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_unary_boolean(exprt &expr)
{
  implicit_typecast_bool(to_unary_expr(expr).op());

  // This is not quite accurate: the standard says the result
  // should be of type 'int'.
  // We do 'bool' anyway to get more compact formulae. Eventually,
  // this should be achieved by means of simplification, and not
  // in the frontend.
  expr.type()=bool_typet();
}

bool c_typecheck_baset::gcc_vector_types_compatible(
  const vector_typet &type0,
  const vector_typet &type1)
{
  // This is relatively restrictive!

  // compare dimension
  const auto s0 = numeric_cast<mp_integer>(type0.size());
  const auto s1 = numeric_cast<mp_integer>(type1.size());
  if(!s0.has_value())
    return false;
  if(!s1.has_value())
    return false;
  if(*s0 != *s1)
    return false;

  // compare subtype
  if(
    (type0.element_type().id() == ID_signedbv ||
     type0.element_type().id() == ID_unsignedbv) &&
    (type1.element_type().id() == ID_signedbv ||
     type1.element_type().id() == ID_unsignedbv) &&
    to_bitvector_type(type0.element_type()).get_width() ==
      to_bitvector_type(type1.element_type()).get_width())
    return true;

  return type0.element_type() == type1.element_type();
}

void c_typecheck_baset::typecheck_expr_binary_arithmetic(exprt &expr)
{
  auto &binary_expr = to_binary_expr(expr);
  exprt &op0 = binary_expr.op0();
  exprt &op1 = binary_expr.op1();

  const typet o_type0 = op0.type();
  const typet o_type1 = op1.type();

  if(o_type0.id()==ID_vector &&
     o_type1.id()==ID_vector)
  {
    if(
      gcc_vector_types_compatible(
        to_vector_type(o_type0), to_vector_type(o_type1)) &&
      is_number(to_vector_type(o_type0).element_type()))
    {
      // Vector arithmetic has fairly strict typing rules, no promotion
      op1 = typecast_exprt::conditional_cast(op1, op0.type());
      expr.type()=op0.type();
      return;
    }
  }
  else if(
    o_type0.id() == ID_vector && o_type1.id() != ID_vector &&
    is_number(o_type1))
  {
    // convert op1 to the vector type
    op1 = typecast_exprt(op1, o_type0);
    expr.type() = o_type0;
    return;
  }
  else if(
    o_type0.id() != ID_vector && o_type1.id() == ID_vector &&
    is_number(o_type0))
  {
    // convert op0 to the vector type
    op0 = typecast_exprt(op0, o_type1);
    expr.type() = o_type1;
    return;
  }

  if(expr.id() == ID_saturating_minus || expr.id() == ID_saturating_plus)
  {
    implicit_typecast(op1, o_type0);
  }
  else
  {
    // promote!
    implicit_typecast_arithmetic(op0, op1);
  }

  const typet &type0 = op0.type();
  const typet &type1 = op1.type();

  if(expr.id()==ID_plus || expr.id()==ID_minus ||
     expr.id()==ID_mult || expr.id()==ID_div)
  {
    if(type0.id()==ID_pointer || type1.id()==ID_pointer)
    {
      typecheck_expr_pointer_arithmetic(expr);
      return;
    }
    else if(type0==type1)
    {
      if(is_number(type0))
      {
        expr.type()=type0;
        return;
      }
    }
  }
  else if(expr.id()==ID_mod)
  {
    if(type0==type1)
    {
      if(type0.id()==ID_signedbv || type0.id()==ID_unsignedbv)
      {
        expr.type()=type0;
        return;
      }
    }
  }
  else if(
    expr.id() == ID_bitand || expr.id() == ID_bitnand ||
    expr.id() == ID_bitxor || expr.id() == ID_bitor)
  {
    if(type0==type1)
    {
      if(is_number(type0))
      {
        expr.type()=type0;
        return;
      }
      else if(type0.id()==ID_bool)
      {
        if(expr.id()==ID_bitand)
          expr.id(ID_and);
        else if(expr.id() == ID_bitnand)
          expr.id(ID_nand);
        else if(expr.id()==ID_bitor)
          expr.id(ID_or);
        else if(expr.id()==ID_bitxor)
          expr.id(ID_xor);
        else
          UNREACHABLE;
        expr.type()=type0;
        return;
      }
    }
  }
  else if(expr.id() == ID_saturating_minus || expr.id() == ID_saturating_plus)
  {
    if(
      type0 == type1 &&
      (type0.id() == ID_signedbv || type0.id() == ID_unsignedbv))
    {
      expr.type() = type0;
      return;
    }
  }

  error().source_location = expr.source_location();
  error() << "operator '" << expr.id() << "' not defined for types '"
          << to_string(o_type0) << "' and '" << to_string(o_type1) << "'"
          << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_shifts(shift_exprt &expr)
{
  assert(expr.id()==ID_shl || expr.id()==ID_shr);

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0 = op0.type();
  const typet o_type1 = op1.type();

  if(o_type0.id()==ID_vector &&
     o_type1.id()==ID_vector)
  {
    if(
      to_vector_type(o_type0).element_type() ==
        to_vector_type(o_type1).element_type() &&
      is_number(to_vector_type(o_type0).element_type()))
    {
      // {a0, a1, ..., an} >> {b0, b1, ..., bn} ==
      // {a0 >> b0, a1 >> b1, ..., an >> bn}
      // Fairly strict typing rules, no promotion
      expr.type()=op0.type();
      return;
    }
  }

  if(
    o_type0.id() == ID_vector &&
    is_number(to_vector_type(o_type0).element_type()) && is_number(o_type1))
  {
    // {a0, a1, ..., an} >> b == {a0 >> b, a1 >> b, ..., an >> b}
    op1 = typecast_exprt(op1, o_type0);
    expr.type()=op0.type();
    return;
  }

  // must do the promotions _separately_!
  implicit_typecast_arithmetic(op0);
  implicit_typecast_arithmetic(op1);

  if(is_number(op0.type()) &&
     is_number(op1.type()))
  {
    expr.type()=op0.type();

    if(expr.id()==ID_shr) // shifting operation depends on types
    {
      const typet &op0_type = op0.type();

      if(op0_type.id()==ID_unsignedbv)
      {
        expr.id(ID_lshr);
        return;
      }
      else if(op0_type.id()==ID_signedbv)
      {
        expr.id(ID_ashr);
        return;
      }
    }

    return;
  }

  error().source_location = expr.source_location();
  error() << "operator '" << expr.id() << "' not defined for types '"
          << to_string(o_type0) << "' and '" << to_string(o_type1) << "'"
          << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_arithmetic_pointer(const exprt &expr)
{
  const typet &type=expr.type();
  PRECONDITION(type.id() == ID_pointer);

  const typet &base_type = to_pointer_type(type).base_type();

  if(
    base_type.id() == ID_struct_tag &&
    follow_tag(to_struct_tag_type(base_type)).is_incomplete())
  {
    error().source_location = expr.source_location();
    error() << "pointer arithmetic with unknown object size" << eom;
    throw 0;
  }
  else if(
    base_type.id() == ID_union_tag &&
    follow_tag(to_union_tag_type(base_type)).is_incomplete())
  {
    error().source_location = expr.source_location();
    error() << "pointer arithmetic with unknown object size" << eom;
    throw 0;
  }
  else if(
    base_type.id() == ID_empty &&
    config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    error().source_location = expr.source_location();
    error() << "pointer arithmetic with unknown object size" << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_expr_pointer_arithmetic(exprt &expr)
{
  auto &binary_expr = to_binary_expr(expr);
  exprt &op0 = binary_expr.op0();
  exprt &op1 = binary_expr.op1();

  const typet &type0 = op0.type();
  const typet &type1 = op1.type();

  if(expr.id()==ID_minus ||
     (expr.id()==ID_side_effect && expr.get(ID_statement)==ID_assign_minus))
  {
    if(type0.id()==ID_pointer &&
       type1.id()==ID_pointer)
    {
      // We should check the subtypes, and complain if
      // they are really different.
      expr.type()=pointer_diff_type();
      typecheck_arithmetic_pointer(op0);
      typecheck_arithmetic_pointer(op1);
      return;
    }

    if(type0.id()==ID_pointer &&
       (type1.id()==ID_bool ||
        type1.id()==ID_c_bool ||
        type1.id()==ID_unsignedbv ||
        type1.id()==ID_signedbv ||
        type1.id()==ID_c_bit_field ||
        type1.id()==ID_c_enum_tag))
    {
      typecheck_arithmetic_pointer(op0);
      make_index_type(op1);
      expr.type()=type0;
      return;
    }
  }
  else if(expr.id()==ID_plus ||
          (expr.id()==ID_side_effect && expr.get(ID_statement)==ID_assign_plus))
  {
    exprt *p_op, *int_op;

    if(type0.id()==ID_pointer)
    {
      p_op=&op0;
      int_op=&op1;
    }
    else if(type1.id()==ID_pointer)
    {
      p_op=&op1;
      int_op=&op0;
    }
    else
    {
      p_op=int_op=nullptr;
      UNREACHABLE;
    }

    const typet &int_op_type = int_op->type();

    if(int_op_type.id()==ID_bool ||
       int_op_type.id()==ID_c_bool ||
       int_op_type.id()==ID_unsignedbv ||
       int_op_type.id()==ID_signedbv ||
       int_op_type.id()==ID_c_bit_field ||
       int_op_type.id()==ID_c_enum_tag)
    {
      typecheck_arithmetic_pointer(*p_op);
      make_index_type(*int_op);
      expr.type()=p_op->type();
      return;
    }
  }

  irep_idt op_name;

  if(expr.id()==ID_side_effect)
    op_name=to_side_effect_expr(expr).get_statement();
  else
    op_name=expr.id();

  error().source_location = expr.source_location();
  error() << "operator '" << op_name << "' not defined for types '"
          << to_string(type0) << "' and '" << to_string(type1) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_binary_boolean(exprt &expr)
{
  auto &binary_expr = to_binary_expr(expr);
  implicit_typecast_bool(binary_expr.op0());
  implicit_typecast_bool(binary_expr.op1());

  // This is not quite accurate: the standard says the result
  // should be of type 'int'.
  // We do 'bool' anyway to get more compact formulae. Eventually,
  // this should be achieved by means of simplification, and not
  // in the frontend.
  expr.type()=bool_typet();
}

void c_typecheck_baset::typecheck_side_effect_assignment(
  side_effect_exprt &expr)
{
  const irep_idt &statement=expr.get_statement();

  auto &binary_expr = to_binary_expr(expr);
  exprt &op0 = binary_expr.op0();
  exprt &op1 = binary_expr.op1();

  {
    const typet &type0=op0.type();

    if(type0.id()==ID_empty)
    {
      error().source_location = expr.source_location();
      error() << "cannot assign void" << eom;
      throw 0;
    }

    if(!op0.get_bool(ID_C_lvalue))
    {
      error().source_location = expr.source_location();
      error() << "assignment error: '" << to_string(op0) << "' not an lvalue"
              << eom;
      throw 0;
    }

    if(type0.get_bool(ID_C_constant))
    {
      error().source_location = expr.source_location();
      error() << "'" << to_string(op0) << "' is constant" << eom;
      throw 0;
    }

    // refuse to assign arrays
    if(type0.id() == ID_array)
    {
      error().source_location = expr.source_location();
      error() << "direct assignments to arrays not permitted" << eom;
      throw 0;
    }
  }

  // Add a cast to the underlying type for bit fields.
  // In particular, sizeof(s.f=1) works for bit fields.
  if(op0.type().id()==ID_c_bit_field)
    op0 = typecast_exprt(op0, op0.type().subtype());

  const typet o_type0=op0.type();
  const typet o_type1=op1.type();

  expr.type()=o_type0;

  if(statement==ID_assign)
  {
    implicit_typecast(op1, o_type0);
    return;
  }
  else if(statement==ID_assign_shl ||
          statement==ID_assign_shr)
  {
    if(o_type0.id() == ID_vector)
    {
      auto &vector_o_type0 = to_vector_type(o_type0);

      if(
        o_type1.id() == ID_vector &&
        vector_o_type0.element_type() ==
          to_vector_type(o_type1).element_type() &&
        is_number(vector_o_type0.element_type()))
      {
        return;
      }
      else if(is_number(vector_o_type0.element_type()) && is_number(o_type1))
      {
        op1 = typecast_exprt(op1, o_type0);
        return;
      }
    }

    implicit_typecast_arithmetic(op0);
    implicit_typecast_arithmetic(op1);

    if(is_number(op0.type()) && is_number(op1.type()))
    {
      if(statement==ID_assign_shl)
      {
        return;
      }
      else // assign_shr
      {
        // distinguish arithmetic from logical shifts by looking at type

        typet underlying_type=op0.type();

        if(underlying_type.id()==ID_unsignedbv ||
           underlying_type.id()==ID_c_bool)
        {
          expr.set(ID_statement, ID_assign_lshr);
          return;
        }
        else if(underlying_type.id()==ID_signedbv)
        {
          expr.set(ID_statement, ID_assign_ashr);
          return;
        }
      }
    }
  }
  else if(statement==ID_assign_bitxor ||
          statement==ID_assign_bitand ||
          statement==ID_assign_bitor)
  {
    // these are more restrictive
    if(o_type0.id()==ID_bool ||
       o_type0.id()==ID_c_bool)
    {
      implicit_typecast_arithmetic(op0, op1);
      if(
        op1.type().id() == ID_bool || op1.type().id() == ID_c_bool ||
        op1.type().id() == ID_c_enum_tag || op1.type().id() == ID_unsignedbv ||
        op1.type().id() == ID_signedbv || op1.type().id() == ID_c_bit_field)
      {
        return;
      }
    }
    else if(o_type0.id()==ID_c_enum_tag ||
            o_type0.id()==ID_unsignedbv ||
            o_type0.id()==ID_signedbv ||
            o_type0.id()==ID_c_bit_field)
    {
      implicit_typecast_arithmetic(op0, op1);
      if(
        op1.type().id() == ID_c_enum_tag || op1.type().id() == ID_unsignedbv ||
        op1.type().id() == ID_signedbv || op1.type().id() == ID_c_bit_field)
      {
        return;
      }
    }
    else if(o_type0.id()==ID_vector &&
            o_type1.id()==ID_vector)
    {
      // We are willing to do a modest amount of conversion
      if(gcc_vector_types_compatible(
           to_vector_type(o_type0), to_vector_type(o_type1)))
      {
        op1 = typecast_exprt::conditional_cast(op1, o_type0);
        return;
      }
    }
    else if(
      o_type0.id() == ID_vector &&
      (o_type1.id() == ID_bool || o_type1.id() == ID_c_bool ||
       o_type1.id() == ID_c_enum_tag || o_type1.id() == ID_unsignedbv ||
       o_type1.id() == ID_signedbv))
    {
      implicit_typecast_arithmetic(op1);
      op1 = typecast_exprt(op1, o_type0);
      return;
    }
  }
  else
  {
    if(o_type0.id()==ID_pointer &&
       (statement==ID_assign_minus || statement==ID_assign_plus))
    {
      typecheck_expr_pointer_arithmetic(expr);
      return;
    }
    else if(o_type0.id()==ID_vector &&
            o_type1.id()==ID_vector)
    {
      // We are willing to do a modest amount of conversion
      if(gcc_vector_types_compatible(
           to_vector_type(o_type0), to_vector_type(o_type1)))
      {
        op1 = typecast_exprt::conditional_cast(op1, o_type0);
        return;
      }
    }
    else if(o_type0.id() == ID_vector)
    {
      implicit_typecast_arithmetic(op1);

      if(
        is_number(op1.type()) || op1.type().id() == ID_bool ||
        op1.type().id() == ID_c_bool || op1.type().id() == ID_c_enum_tag)
      {
        op1 = typecast_exprt(op1, o_type0);
        return;
      }
    }
    else if(o_type0.id()==ID_bool ||
            o_type0.id()==ID_c_bool)
    {
      implicit_typecast_arithmetic(op0, op1);
      if(op1.type().id()==ID_bool ||
         op1.type().id()==ID_c_bool ||
         op1.type().id()==ID_c_enum_tag ||
         op1.type().id()==ID_unsignedbv ||
         op1.type().id()==ID_signedbv)
        return;
    }
    else
    {
      implicit_typecast_arithmetic(op0, op1);

      if(is_number(op1.type()) ||
         op1.type().id()==ID_bool ||
         op1.type().id()==ID_c_bool ||
         op1.type().id()==ID_c_enum_tag)
        return;
    }
  }

  error().source_location = expr.source_location();
  error() << "assignment '" << statement << "' not defined for types '"
          << to_string(o_type0) << "' and '" << to_string(o_type1) << "'"
          << eom;

  throw 0;
}

class is_compile_time_constantt : public is_constantt
{
public:
  explicit is_compile_time_constantt(const namespacet &ns) : ns(ns)
  {
  }

protected:
  const namespacet &ns;

  bool is_constant(const exprt &e) const override
  {
    if(e.id() == ID_infinity)
      return true;
    else
      return is_constantt::is_constant(e);
  }

  bool is_constant_address_of(const exprt &e) const override
  {
    if(e.id() == ID_symbol)
    {
      return e.type().id() == ID_code ||
             ns.lookup(to_symbol_expr(e).get_identifier()).is_static_lifetime;
    }
    else if(e.id() == ID_array && e.get_bool(ID_C_string_constant))
      return true;
    else
      return is_constantt::is_constant_address_of(e);
  }
};

void c_typecheck_baset::make_constant(exprt &expr)
{
  // Floating-point expressions may require a rounding mode.
  // ISO 9899:1999 F.7.2 says that the default is "round to nearest".
  // Some compilers have command-line options to override.
  const auto rounding_mode =
    from_integer(ieee_floatt::ROUND_TO_EVEN, signed_int_type());
  adjust_float_expressions(expr, rounding_mode);

  simplify(expr, *this);

  if(!is_compile_time_constantt(*this)(expr))
  {
    error().source_location=expr.find_source_location();
    error() << "expected constant expression, but got '" << to_string(expr)
            << "'" << eom;
    throw 0;
  }
}

void c_typecheck_baset::make_constant_index(exprt &expr)
{
  make_constant(expr);
  make_index_type(expr);
  simplify(expr, *this);

  if(!is_compile_time_constantt(*this)(expr))
  {
    error().source_location=expr.find_source_location();
    error() << "conversion to integer constant failed" << eom;
    throw 0;
  }
}

void c_typecheck_baset::disallow_subexpr_by_id(
  const exprt &expr,
  const irep_idt &id,
  const std::string &message) const
{
  if(!has_subexpr(expr, id))
    return;

  error().source_location = expr.source_location();
  error() << message << eom;
  throw 0;
}
