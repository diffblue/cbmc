/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#include "c_typecheck_base.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/ieee_float.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/string_constant.h>

#include <goto-programs/adjust_float_expressions.h>

#include "builtin_factory.h"
#include "c_typecast.h"
#include "c_qualifiers.h"
#include "anonymous_member.h"
#include "padding.h"

void c_typecheck_baset::typecheck_expr(exprt &expr)
{
  if(expr.id()==ID_already_typechecked)
  {
    assert(expr.operands().size()==1);
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return;
  }

  // fist do sub-nodes
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

      expr.op2()=from_integer(0, unsigned_int_type());
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
    else if(type2==type1.subtype())
      return true;
  }
  else if(type2.id()==ID_c_enum)
  {
    if(type1==type2.subtype())
      return true;
  }
  else if(type1.id()==ID_pointer &&
          type2.id()==ID_pointer)
  {
    return gcc_types_compatible_p(type1.subtype(), type2.subtype());
  }
  else if(type1.id()==ID_array &&
          type2.id()==ID_array)
  {
    return
      gcc_types_compatible_p(type1.subtype(), type2.subtype()); // ignore size
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
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()==ID_mult || expr.id()==ID_div ||
          expr.id()==ID_mod ||
          expr.id()==ID_bitand || expr.id()==ID_bitxor || expr.id()==ID_bitor)
    typecheck_expr_binary_arithmetic(expr);
  else if(expr.id()==ID_shl || expr.id()==ID_shr)
    typecheck_expr_shifts(to_shift_expr(expr));
  else if(expr.id()==ID_comma)
    typecheck_expr_comma(expr);
  else if(expr.id()==ID_if)
    typecheck_expr_trinary(to_if_expr(expr));
  else if(expr.id()==ID_code)
  {
    err_location(expr);
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

    expr.make_bool(gcc_types_compatible_p(subtypes[0], subtypes[1]));
    expr.add_source_location()=source_location;
  }
  else if(expr.id()==ID_clang_builtin_convertvector)
  {
    // This has one operand and a type, and acts like a typecast
    DATA_INVARIANT(expr.operands().size()==1, "clang_builtin_convertvector has one operand");
    typecheck_type(expr.type());
    typecast_exprt tmp(expr.op0(), expr.type());
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
      {
        assert(it->operands().size()==1);
        typecheck_expr(it->op0()); // still needs typechecking
      }
    }
  }
  else if(expr.id()==ID_initializer_list)
  {
    // already fine, just set some type
    expr.type()=void_type();
  }
  else if(expr.id()==ID_forall ||
          expr.id()==ID_exists)
  {
    // op0 is a declaration,
    // op1 the bound expression
    assert(expr.operands().size()==2);
    expr.type()=bool_typet();

    if(expr.op0().get(ID_statement)!=ID_decl)
    {
      err_location(expr);
      error() << "expected declaration as operand of quantifier" << eom;
      throw 0;
    }

    if(has_subexpr(expr.op1(), ID_side_effect))
    {
      err_location(expr);
      error() << "quantifier must not contain side effects" << eom;
      throw 0;
    }

    // replace declaration by symbol expression
    symbol_exprt bound=to_symbol_expr(expr.op0().op0());
    expr.op0().swap(bound);

    implicit_typecast_bool(expr.op1());
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
    INVARIANT(
      expr.operands().size() == 1,
      "real part retrieval operation should have one operand");

    exprt op = expr.op0();
    op.type() = follow(op.type());

    if(op.type().id() != ID_complex)
    {
      if(!is_number(op.type()))
      {
        err_location(op);
        error() << "real part retrieval expects numerical operand, "
                << "but got `" << to_string(op.type()) << "'" << eom;
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
    INVARIANT(
      expr.operands().size() == 1,
      "imaginary part retrieval operation should have one operand");

    exprt op = expr.op0();
    op.type() = follow(op.type());

    if(op.type().id() != ID_complex)
    {
      if(!is_number(op.type()))
      {
        err_location(op);
        error() << "real part retrieval expects numerical operand, "
                << "but got `" << to_string(op.type()) << "'" << eom;
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

    if(expr.operands().size()!=1)
    {
      err_location(expr);
      error() << "_Generic expects one operand" << eom;
      throw 0;
    }

    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(follow(expr.op0().type()).id()==ID_bool)
      expr.op0().make_typecast(signed_int_type());

    irept::subt &generic_associations=
      expr.add(ID_generic_associations).get_sub();

    // first typecheck all types
    Forall_irep(it, generic_associations)
      if(it->get(ID_type_arg)!=ID_default)
      {
        typet &type=static_cast<typet &>(it->add(ID_type_arg));
        typecheck_type(type);
      }

    // first try non-default match
    exprt default_match=nil_exprt();
    exprt assoc_match=nil_exprt();

    const typet &op_type=follow(expr.op0().type());

    forall_irep(it, generic_associations)
    {
      if(it->get(ID_type_arg)==ID_default)
        default_match=static_cast<const exprt &>(it->find(ID_value));
      else if(op_type==
              follow(static_cast<const typet &>(it->find(ID_type_arg))))
        assoc_match=static_cast<const exprt &>(it->find(ID_value));
    }

    if(assoc_match.is_nil())
    {
      if(default_match.is_not_nil())
        expr.swap(default_match);
      else
      {
        err_location(expr);
        error() << "unmatched generic selection: "
                << to_string(expr.op0().type()) << eom;
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
  else
  {
    err_location(expr);
    error() << "unexpected expression: " << expr.pretty() << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_expr_comma(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    error() << "comma operator expects two operands" << eom;
    throw 0;
  }

  expr.type()=expr.op1().type();

  // make this an l-value if the last operand is one
  if(expr.op1().get_bool(ID_C_lvalue))
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

  assert(expr.operands().size()==1);
  exprt arg=expr.op0();

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
    err_location(expr);
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
        err_location(expr);
        error() << "offsetof of member expects struct/union type, "
                << "but got `" << to_string(type) << "'" << eom;
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
            exprt o=
              member_offset_expr(
                to_struct_type(type), component_name, *this);

            if(o.is_nil())
            {
              err_location(expr);
              error() << "offsetof failed to determine offset of `"
                      << component_name << "'" << eom;
              throw 0;
            }

            if(o.type()!=size_type())
              o.make_typecast(size_type());

            result=plus_exprt(result, o);
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
              c.get_anonymous() && (follow(c.type()).id() == ID_struct ||
                                    follow(c.type()).id() == ID_union))
            {
              if(has_component_rec(c.type(), component_name, *this))
              {
                if(type.id()==ID_struct)
                {
                  exprt o = member_offset_expr(
                    to_struct_type(type), c.get_name(), *this);

                  if(o.is_nil())
                  {
                    err_location(expr);
                    error() << "offsetof failed to determine offset of `"
                            << component_name << "'" << eom;
                    throw 0;
                  }

                  if(o.type()!=size_type())
                    o.make_typecast(size_type());

                  result=plus_exprt(result, o);
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
            err_location(expr);
            error() << "offset-of of member failed to find component `"
                    << component_name << "' in `"
                    << to_string(type) << "'" << eom;
            throw 0;
          }
        }
      }
    }
    else if(m_it->id()==ID_index)
    {
      assert(m_it->operands().size()==1);

      if(type.id()!=ID_array)
      {
        err_location(expr);
        error() << "offsetof of index expects array type" << eom;
        throw 0;
      }

      exprt index=m_it->op0();

      // still need to typecheck index
      typecheck_expr(index);

      exprt sub_size=size_of_expr(type.subtype(), *this);
      if(index.type()!=size_type())
        index.make_typecast(size_type());
      result=plus_exprt(result, mult_exprt(sub_size, index));

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
    assert(expr.operands().size()==2);

    typecheck_expr(expr.op1()); // arguments
  }
  else if(expr.id()==ID_side_effect &&
          expr.get(ID_statement)==ID_statement_expression)
  {
    typecheck_code(to_code(expr.op0()));
  }
  else if(expr.id()==ID_forall || expr.id()==ID_exists)
  {
    assert(expr.operands().size()==2);

    ansi_c_declarationt &declaration=
      to_ansi_c_declaration(expr.op0());

    typecheck_declaration(declaration);

    if(declaration.declarators().size()!=1)
    {
      err_location(expr);
      error() << "expected one declarator exactly" << eom;
      throw 0;
    }

    irep_idt identifier=
      declaration.declarators().front().get_name();

    // look it up
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);

    if(s_it==symbol_table.symbols.end())
    {
      err_location(expr);
      error() << "failed to find decl symbol `" << identifier
              << "' in symbol table" << eom;
      throw 0;
    }

    const symbolt &symbol=s_it->second;

    if(symbol.is_type || symbol.is_extern || symbol.is_static_lifetime ||
       !is_complete_type(symbol.type) || symbol.type.id()==ID_code)
    {
      err_location(expr);
      error() << "unexpected quantified symbol" << eom;
      throw 0;
    }

    code_declt decl(symbol.symbol_expr());
    decl.add_source_location()=declaration.source_location();

    expr.op0()=decl;

    typecheck_expr(expr.op1());
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
    err_location(expr);
    error() << "failed to find symbol `"
            << identifier << "'" << eom;
    throw 0;
  }

  const symbolt &symbol=*symbol_ptr;

  if(symbol.is_type)
  {
    err_location(expr);
    error() << "did not expect a type symbol here, but got `"
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
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "statement expression expects one operand" << eom;
    throw 0;
  }

  codet &code=to_code(expr.op0());

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
  else if(last_statement==ID_function_call)
  {
    // this is suspected to be dead
    UNREACHABLE;

    // make the last statement an expression

    code_function_callt &fc=to_code_function_call(last);

    side_effect_expr_function_callt sideeffect(
      fc.function(),
      fc.arguments(),
      to_code_type(fc.function().type()).return_type(),
      fc.source_location());

    expr.type()=sideeffect.type();

    if(fc.lhs().is_nil())
    {
      code_expressiont code_expr(sideeffect);
      code_expr.add_source_location() = fc.source_location();
      last.swap(code_expr);
    }
    else
    {
      side_effect_exprt assign(
        ID_assign, sideeffect.type(), fc.source_location());
      assign.move_to_operands(fc.lhs(), sideeffect);

      code_expressiont code_expr(assign);
      code_expr.add_source_location() = fc.source_location();

      last.swap(code_expr);
    }
  }
  else
    expr.type()=typet(ID_empty);
}

void c_typecheck_baset::typecheck_expr_sizeof(exprt &expr)
{
  typet type;

  if(expr.operands().empty())
  {
    type.swap(static_cast<typet &>(expr.add(ID_type_arg)));
    typecheck_type(type);
  }
  else if(expr.operands().size()==1)
  {
    type.swap(expr.op0().type());
  }
  else
  {
    err_location(expr);
    error() << "sizeof operator expects zero or one operand, "
               "but got " << expr.operands().size() << eom;
    throw 0;
  }

  exprt new_expr;

  if(type.id()==ID_c_bit_field)
  {
    err_location(expr);
    error() << "sizeof cannot be applied to bit fields" << eom;
    throw 0;
  }
  else if(type.id() == ID_bool)
  {
    err_location(expr);
    error() << "sizeof cannot be applied to single bits" << eom;
    throw 0;
  }
  else if(type.id() == ID_empty)
  {
    // This is a gcc extension.
    // https://gcc.gnu.org/onlinedocs/gcc-4.8.0/gcc/Pointer-Arith.html
    new_expr = size_of_expr(char_type(), *this);
  }
  else
  {
    new_expr = size_of_expr(type, *this);

    if(new_expr.is_nil())
    {
      err_location(expr);
      error() << "type has no size: " << to_string(type) << eom;
      throw 0;
    }
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
    argument_type=expr.op0().type();
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
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "typecast operator expects one operand" << eom;
    throw 0;
  }

  exprt &op=expr.op0();

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

  const typet expr_type=follow(expr.type());

  if(expr_type.id()==ID_union &&
     !base_type_eq(expr_type, op.type(), *this) &&
     op.id()!=ID_initializer_list)
  {
    // This is a GCC extension. It's either a 'temporary union',
    // where the argument is one of the member types.

    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(follow(op.type()).id()==ID_bool)
      op.make_typecast(signed_int_type());

    // we need to find a member with the right type
    for(const auto &c : to_union_type(expr_type).components())
    {
      if(base_type_eq(c.type(), op.type(), *this))
      {
        // found! build union constructor
        union_exprt union_expr(expr.type());
        union_expr.add_source_location()=expr.source_location();
        union_expr.op()=op;
        union_expr.set_component_name(c.get_name());
        expr=union_expr;
        expr.set(ID_C_lvalue, true);
        return;
      }
    }

    // not found, complain
    err_location(expr);
    error() << "type cast to union: type `"
            << to_string(op.type()) << "' not found in union" << eom;
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

  const typet op_type=follow(op.type());

  // cast to same type?
  if(base_type_eq(expr_type, op_type, *this))
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
    err_location(expr);
    error() << "type cast to `"
            << to_string(expr_type) << "' is not permitted" << eom;
    throw 0;
  }

  if(is_numeric_type(op_type) || op_type.id()==ID_pointer)
  {
  }
  else if(op_type.id()==ID_array)
  {
    index_exprt index;
    index.array()=op;
    index.index()=from_integer(0, index_type());
    index.type()=op_type.subtype();
    op=address_of_exprt(index);
  }
  else if(op_type.id()==ID_empty)
  {
    if(expr_type.id()!=ID_empty)
    {
      err_location(expr);
      error() << "type cast from void only permitted to void, but got `"
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
      err_location(expr);
      error() << "type cast from vector to `"
              << to_string(expr.type()) << "' not permitted" << eom;
      throw 0;
    }
  }
  else
  {
    err_location(expr);
    error() << "type cast from `"
            << to_string(op_type) << "' not permitted" << eom;
    throw 0;
  }

  // The new thing is an lvalue if the previous one is
  // an lvalue and it's just a pointer type cast.
  // This isn't really standard conformant!
  // Note that gcc says "warning: target of assignment not really an lvalue;
  // this will be a hard error in the future", i.e., we
  // can hope that the code below will one day simply go away.

  // Current versions of gcc in fact refuse to do this! Yay!

  if(expr.op0().get_bool(ID_C_lvalue))
  {
    if(expr_type.id()==ID_pointer)
      expr.set(ID_C_lvalue, true);
  }
}

void c_typecheck_baset::make_index_type(exprt &expr)
{
  implicit_typecast(expr, index_type());
}

void c_typecheck_baset::typecheck_expr_index(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  exprt &array_expr=expr.op0();
  exprt &index_expr=expr.op1();

  // we might have to swap them

  {
    const typet &array_full_type=follow(array_expr.type());
    const typet &index_full_type=follow(index_expr.type());

    if(array_full_type.id()!=ID_array &&
       array_full_type.id()!=ID_pointer &&
       array_full_type.id()!=ID_vector &&
       (index_full_type.id()==ID_array ||
        index_full_type.id()==ID_pointer ||
        index_full_type.id()==ID_vector))
      std::swap(array_expr, index_expr);
  }

  make_index_type(index_expr);

  // array_expr is a reference to one of expr.operands(), when that vector is
  // swapped below the reference is no longer valid. final_array_type exists
  // beyond that point so can't be a reference
  const typet final_array_type = follow(array_expr.type());

  if(final_array_type.id()==ID_array ||
     final_array_type.id()==ID_vector)
  {
    expr.type() = final_array_type.subtype();

    if(array_expr.get_bool(ID_C_lvalue))
      expr.set(ID_C_lvalue, true);

    if(final_array_type.get_bool(ID_C_constant))
      expr.type().set(ID_C_constant, true);
  }
  else if(final_array_type.id()==ID_pointer)
  {
    // p[i] is syntactic sugar for *(p+i)

    typecheck_arithmetic_pointer(expr.op0());
    exprt addition(ID_plus, array_expr.type());
    addition.operands().swap(expr.operands());
    expr.move_to_operands(addition);
    expr.id(ID_dereference);
    expr.set(ID_C_lvalue, true);
    expr.type() = final_array_type.subtype();
  }
  else
  {
    err_location(expr);
    error() << "operator [] must take array/vector or pointer but got `"
            << to_string(array_expr.type()) << "'" << eom;
    throw 0;
  }
}

void c_typecheck_baset::adjust_float_rel(exprt &expr)
{
  // equality and disequality on float is not mathematical equality!
  assert(expr.operands().size()==2);

  if(follow(expr.op0().type()).id()==ID_floatbv)
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

  if(follow(o_type0).id()==ID_vector ||
     follow(o_type1).id()==ID_vector)
  {
    typecheck_expr_rel_vector(expr);
    return;
  }

  expr.type()=bool_typet();

  if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    if(follow(o_type0)==follow(o_type1))
    {
      const typet &final_type=follow(o_type0);
      if(final_type.id()!=ID_array &&
         final_type.id()!=ID_incomplete_struct)
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
      op1=constant_exprt(ID_NULL, type0);
      return;
    }

    if(type1.id()==ID_pointer &&
       simplify_expr(op0, *this).is_zero())
    {
      op0=constant_exprt(ID_NULL, type1);
      return;
    }

    // pointer and integer
    if(type0.id()==ID_pointer && is_number(type1))
    {
      op1.make_typecast(type0);
      return;
    }

    if(type1.id()==ID_pointer && is_number(type0))
    {
      op0.make_typecast(type1);
      return;
    }

    if(type0.id()==ID_pointer && type1.id()==ID_pointer)
    {
      op1.make_typecast(type0);
      return;
    }
  }

  err_location(expr);
  error() << "operator `" << expr.id()
          << "' not defined for types `"
          << to_string(o_type0) << "' and `"
          << to_string(o_type1) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_rel_vector(
  binary_relation_exprt &expr)
{
  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=follow(op0.type());
  const typet o_type1=follow(op1.type());

  if(o_type0.id()!=ID_vector ||
     o_type1.id()!=ID_vector ||
     follow(o_type0.subtype())!=follow(o_type1.subtype()))
  {
    err_location(expr);
    error() << "vector operator `" << expr.id()
            << "' not defined for types `"
            << to_string(o_type0) << "' and `"
            << to_string(o_type1) << "'" << eom;
    throw 0;
  }

  // Comparisons between vectors produce a vector
  // of integers with the same dimension.
  expr.type()=vector_typet(signed_int_type(), to_vector_type(o_type0).size());
}

void c_typecheck_baset::typecheck_expr_ptrmember(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "ptrmember operator expects one operand" << eom;
    throw 0;
  }

  const typet &final_op0_type=follow(expr.op0().type());

  if(final_op0_type.id()==ID_array)
  {
    // a->f is the same as a[0].f
    exprt zero=from_integer(0, index_type());
    index_exprt index_expr(expr.op0(), zero, final_op0_type.subtype());
    index_expr.set(ID_C_lvalue, true);
    expr.op0().swap(index_expr);
  }
  else if(final_op0_type.id()==ID_pointer)
  {
    // turn x->y into (*x).y
    dereference_exprt deref_expr(expr.op0());
    deref_expr.add_source_location()=expr.source_location();
    typecheck_expr_dereference(deref_expr);
    expr.op0().swap(deref_expr);
  }
  else
  {
    err_location(expr);
    error() << "ptrmember operator requires pointer or array type "
               "on left hand side, but got `"
            << to_string(expr.op0().type()) << "'" << eom;
    throw 0;
  }

  expr.id(ID_member);
  typecheck_expr_member(expr);
}

void c_typecheck_baset::typecheck_expr_member(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "member operator expects one operand" << eom;
    throw 0;
  }

  exprt &op0=expr.op0();
  typet type=op0.type();

  type = follow(type);

  if(type.id()==ID_incomplete_struct)
  {
    err_location(expr);
    error() << "member operator got incomplete struct type "
               "on left hand side" << eom;
    throw 0;
  }

  if(type.id()==ID_incomplete_union)
  {
    err_location(expr);
    error() << "member operator got incomplete union type "
               "on left hand side" << eom;
    throw 0;
  }

  if(type.id()!=ID_struct &&
     type.id()!=ID_union)
  {
    err_location(expr);
    error() << "member operator requires structure type "
               "on left hand side but got `"
            << to_string(type) << "'" << eom;
    throw 0;
  }

  const struct_union_typet &struct_union_type=
    to_struct_union_type(type);

  const irep_idt &component_name=
    expr.get(ID_component_name);

  // first try to find directly
  struct_union_typet::componentt component=
    struct_union_type.get_component(component_name);

  // if that fails, search the anonymous members

  if(component.is_nil())
  {
    exprt tmp=get_component_rec(op0, component_name, *this);

    if(tmp.is_nil())
    {
      // give up
      err_location(expr);
      error() << "member `" << component_name
              << "' not found in `"
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
    err_location(expr);
    error() << "member `" << component_name
            << "' is " << access << eom;
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
  implicit_typecast_arithmetic(operands[1], operands[2]);

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
    if(operands[1].type().subtype().id()==ID_empty &&
       tmp1.is_constant() &&
       to_constant_expr(tmp1).get_value()==ID_NULL)
      implicit_typecast(operands[1], operands[2].type());
    else if(operands[2].type().subtype().id()==ID_empty &&
            tmp2.is_constant() &&
            to_constant_expr(tmp2).get_value()==ID_NULL)
      implicit_typecast(operands[2], operands[1].type());
    else if(operands[1].type().subtype().id()!=ID_code ||
            operands[2].type().subtype().id()!=ID_code)
    {
      // Make it void *.
      // gcc and clang issue a warning for this.
      expr.type()=pointer_type(empty_typet());
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

  if(follow(operands[1].type())==follow(operands[2].type()))
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

  err_location(expr);
  error() << "operator ?: not defined for types `"
          << to_string(o_type1) << "' and `"
          << to_string(o_type2) << "'" << eom;
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
    err_location(expr);
    error() << "gcc conditional_expr expects two operands" << eom;
    throw 0;
  }

  // use typechecking code for "if"

  if_exprt if_expr;
  if_expr.cond()=operands[0];
  if_expr.true_case()=operands[0];
  if_expr.false_case()=operands[1];
  if_expr.add_source_location()=expr.source_location();

  typecheck_expr_trinary(if_expr);

  // copy the result
  expr.op0()=if_expr.op1();
  expr.op1()=if_expr.op2();
  expr.type()=if_expr.type();
}

void c_typecheck_baset::typecheck_expr_address_of(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "unary operator & expects one operand" << eom;
    throw 0;
  }

  exprt &op=expr.op0();

  if(op.type().id()==ID_c_bit_field)
  {
    err_location(expr);
    error() << "cannot take address of a bit field" << eom;
    throw 0;
  }

  if(op.type().id() == ID_bool)
  {
    err_location(expr);
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

  if(op.id()==ID_address_of &&
     op.get_bool(ID_C_implicit) &&
     op.operands().size()==1 &&
     op.op0().type().id()==ID_code)
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
    err_location(expr);
    error() << "address_of error: `" << to_string(op)
            << "' not an lvalue" << eom;
    throw 0;
  }

  expr.type()=pointer_type(op.type());
}

void c_typecheck_baset::typecheck_expr_dereference(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "unary operator * expects one operand" << eom;
    throw 0;
  }

  exprt &op=expr.op0();

  const typet op_type=follow(op.type());

  if(op_type.id()==ID_array)
  {
    // *a is the same as a[0]
    expr.id(ID_index);
    expr.type()=op_type.subtype();
    expr.copy_to_operands(from_integer(0, index_type()));
    assert(expr.operands().size()==2);
  }
  else if(op_type.id()==ID_pointer)
  {
    expr.type()=op_type.subtype();
  }
  else
  {
    err_location(expr);
    error() << "operand of unary * `" << to_string(op)
            << "' is not a pointer, but got `"
            << to_string(op_type) << "'" << eom;
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
    if(expr.operands().size()!=1)
    {
      err_location(expr);
      error() << statement << "operator expects one operand" << eom;
    }

    const exprt &op0=expr.op0();
    const typet &type0=op0.type();
    const typet &final_type0=follow(type0);

    if(!op0.get_bool(ID_C_lvalue))
    {
      err_location(op0);
      error() << "prefix operator error: `" << to_string(op0)
              << "' not an lvalue" << eom;
      throw 0;
    }

    if(type0.get_bool(ID_C_constant))
    {
      err_location(op0);
      error() << "error: `" << to_string(op0)
              << "' is constant" << eom;
      throw 0;
    }

    if(final_type0.id()==ID_c_enum_tag)
    {
      if(follow_tag(to_c_enum_tag_type(final_type0)).id()==
         ID_incomplete_c_enum)
      {
        err_location(expr);
        error() << "operator `" << statement
                << "' given incomplete type `"
                << to_string(type0) << "'" << eom;
        throw 0;
      }
      else
        expr.type()=type0;
    }
    else if(final_type0.id()==ID_c_bit_field)
    {
      // promote to underlying type
      typet underlying_type=to_c_bit_field_type(final_type0).subtype();
      expr.op0().make_typecast(underlying_type);
      expr.type()=underlying_type;
    }
    else if(is_numeric_type(final_type0))
    {
      expr.type()=type0;
    }
    else if(final_type0.id()==ID_pointer)
    {
      expr.type()=type0;
      typecheck_arithmetic_pointer(op0);
    }
    else
    {
      err_location(expr);
      error() << "operator `" << statement
              << "' not defined for type `"
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
    err_location(expr);
    error() << "unknown side effect: " << statement << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
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
        warning() << "function `" << identifier << "' is not declared" << eom;
      }
    }
  }

  // typecheck it now
  typecheck_expr(f_op);

  const typet f_op_type=follow(f_op.type());

  if(f_op_type.id()!=ID_pointer)
  {
    err_location(f_op);
    error() << "expected function/function pointer as argument but got `"
            << to_string(f_op_type) << "'" << eom;
    throw 0;
  }

  // do implicit dereference
  if(f_op.id()==ID_address_of &&
     f_op.get_bool(ID_C_implicit) &&
     f_op.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(f_op.op0());
    f_op.swap(tmp);
  }
  else
  {
    dereference_exprt tmp(f_op, f_op_type.subtype());
    tmp.set(ID_C_implicit, true);
    tmp.add_source_location()=f_op.source_location();
    f_op.swap(tmp);
  }

  if(f_op.type().id()!=ID_code)
  {
    err_location(f_op);
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

  if(identifier==CPROVER_PREFIX "same_object")
  {
    if(expr.arguments().size()!=2)
    {
      err_location(f_op);
      error() << "same_object expects two operands" << eom;
      throw 0;
    }

    exprt same_object_expr=
      same_object(expr.arguments()[0], expr.arguments()[1]);
    same_object_expr.add_source_location()=source_location;

    return same_object_expr;
  }
  else if(identifier==CPROVER_PREFIX "get_must")
  {
    if(expr.arguments().size()!=2)
    {
      err_location(f_op);
      error() << "get_must expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    binary_predicate_exprt get_must_expr(
      expr.arguments()[0], "get_must", expr.arguments()[1]);
    get_must_expr.add_source_location()=source_location;

    return std::move(get_must_expr);
  }
  else if(identifier==CPROVER_PREFIX "get_may")
  {
    if(expr.arguments().size()!=2)
    {
      err_location(f_op);
      error() << "get_may expects two operands" << eom;
      throw 0;
    }

    typecheck_function_call_arguments(expr);

    binary_predicate_exprt get_may_expr(
      expr.arguments()[0], "get_may", expr.arguments()[1]);
    get_may_expr.add_source_location()=source_location;

    return std::move(get_may_expr);
  }
  else if(identifier==CPROVER_PREFIX "invalid_pointer")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << "invalid_pointer expects one operand" << eom;
      throw 0;
    }

    exprt same_object_expr = invalid_pointer(expr.arguments().front());
    same_object_expr.add_source_location()=source_location;

    return same_object_expr;
  }
  else if(identifier==CPROVER_PREFIX "buffer_size")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << "buffer_size expects one operand" << eom;
      throw 0;
    }

    exprt buffer_size_expr("buffer_size", size_type());
    buffer_size_expr.operands()=expr.arguments();
    buffer_size_expr.add_source_location()=source_location;

    return buffer_size_expr;
  }
  else if(identifier==CPROVER_PREFIX "is_zero_string")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << "is_zero_string expects one operand" << eom;
      throw 0;
    }

    predicate_exprt is_zero_string_expr("is_zero_string");
    is_zero_string_expr.operands()=expr.arguments();
    is_zero_string_expr.set(ID_C_lvalue, true); // make it an lvalue
    is_zero_string_expr.add_source_location()=source_location;

    return std::move(is_zero_string_expr);
  }
  else if(identifier==CPROVER_PREFIX "zero_string_length")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << "zero_string_length expects one operand" << eom;
      throw 0;
    }

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
      err_location(f_op);
      error() << "dynamic_object expects one argument" << eom;
      throw 0;
    }

    exprt dynamic_object_expr=exprt(ID_dynamic_object, expr.type());
    dynamic_object_expr.operands()=expr.arguments();
    dynamic_object_expr.add_source_location()=source_location;

    return dynamic_object_expr;
  }
  else if(identifier==CPROVER_PREFIX "POINTER_OFFSET")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << "pointer_offset expects one argument" << eom;
      throw 0;
    }

    exprt pointer_offset_expr=pointer_offset(expr.arguments().front());
    pointer_offset_expr.add_source_location()=source_location;

    return typecast_exprt::conditional_cast(pointer_offset_expr, expr.type());
  }
  else if(identifier == CPROVER_PREFIX "OBJECT_SIZE")
  {
    if(expr.arguments().size() != 1)
    {
      err_location(f_op);
      error() << "object_size expects one operand" << eom;
      throw 0;
    }

    unary_exprt object_size_expr(
      ID_object_size, expr.arguments()[0], size_type());
    object_size_expr.add_source_location() = source_location;

    return std::move(object_size_expr);
  }
  else if(identifier==CPROVER_PREFIX "POINTER_OBJECT")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << "pointer_object expects one argument" << eom;
      throw 0;
    }

    exprt pointer_object_expr = pointer_object(expr.arguments().front());
    pointer_object_expr.add_source_location() = source_location;

    return typecast_exprt::conditional_cast(pointer_object_expr, expr.type());
  }
  else if(identifier=="__builtin_bswap16" ||
          identifier=="__builtin_bswap32" ||
          identifier=="__builtin_bswap64")
  {
    typecheck_function_call_arguments(expr);

    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    // these are hard-wired to 8 bits according to the gcc manual
    bswap_exprt bswap_expr(expr.arguments().front(), 8, expr.type());
    bswap_expr.add_source_location()=source_location;

    return std::move(bswap_expr);
  }
  else if(identifier=="__builtin_nontemporal_load")
  {
    typecheck_function_call_arguments(expr);

    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    // these return the subtype of the argument
    exprt &ptr_arg=expr.arguments().front();

    if(ptr_arg.type().id()!=ID_pointer)
    {
      err_location(f_op);
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
      err_location(f_op);
      error() << identifier << " expects six arguments" << eom;
      throw 0;
    }

    // This gets 5 integers followed by a float or double.
    // The five integers are the return values for the cases
    // FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL and FP_ZERO.
    // gcc expects this to be able to produce compile-time constants.

    const exprt &fp_value = expr.arguments()[5];

    if(fp_value.type().id() != ID_floatbv)
    {
      err_location(fp_value);
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
      err_location(f_op);
      error() << "isnan expects one operand" << eom;
      throw 0;
    }

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
      err_location(f_op);
      error() << "isfinite expects one operand" << eom;
      throw 0;
    }

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
      err_location(f_op);
      error() << "abs-functions expect one operand" << eom;
      throw 0;
    }

    abs_exprt abs_expr(expr.arguments().front());
    abs_expr.add_source_location()=source_location;

    return std::move(abs_expr);
  }
  else if(identifier==CPROVER_PREFIX "allocate")
  {
    if(expr.arguments().size()!=2)
    {
      err_location(f_op);
      error() << "allocate expects two operands" << eom;
      throw 0;
    }

    side_effect_exprt malloc_expr(ID_allocate, expr.type(), source_location);
    malloc_expr.operands()=expr.arguments();

    return std::move(malloc_expr);
  }
  else if(
    identifier == CPROVER_PREFIX "r_ok" || identifier == CPROVER_PREFIX "w_ok")
  {
    if(expr.arguments().size() != 2)
    {
      err_location(f_op);
      error() << identifier << " expects two operands" << eom;
      throw 0;
    }

    irep_idt id = identifier == CPROVER_PREFIX "r_ok" ? ID_r_ok : ID_w_ok;

    predicate_exprt ok_expr(id, expr.arguments()[0], expr.arguments()[1]);
    ok_expr.add_source_location() = source_location;

    return std::move(ok_expr);
  }
  else if(identifier==CPROVER_PREFIX "isinff" ||
          identifier==CPROVER_PREFIX "isinfd" ||
          identifier==CPROVER_PREFIX "isinfld" ||
          identifier=="__builtin_isinf")
  {
    if(expr.arguments().size()!=1)
    {
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
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
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    // returns 1 for +inf and -1 for -inf, and 0 otherwise

    const exprt &fp_value = expr.arguments().front();

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
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    const exprt &fp_value = expr.arguments()[0];

    if(fp_value.type().id() != ID_floatbv)
    {
      err_location(fp_value);
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
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

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
      err_location(f_op);
      error() << identifier << " expects one operand" << eom;
      throw 0;
    }

    popcount_exprt popcount_expr(expr.arguments().front(), expr.type());
    popcount_expr.add_source_location()=source_location;

    return std::move(popcount_expr);
  }
  else if(identifier==CPROVER_PREFIX "equal")
  {
    if(expr.arguments().size()!=2)
    {
      err_location(f_op);
      error() << "equal expects two operands" << eom;
      throw 0;
    }

    equal_exprt equality_expr;
    equality_expr.operands()=expr.arguments();
    equality_expr.add_source_location()=source_location;

    if(!base_type_eq(equality_expr.lhs().type(),
                     equality_expr.rhs().type(), *this))
    {
      err_location(f_op);
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
      err_location(f_op);
      error() << "__builtin_expect expects two arguments" << eom;
      throw 0;
    }

    return typecast_exprt(expr.arguments()[0], expr.type());
  }
  else if(identifier=="__builtin_object_size")
  {
    // this is a gcc extension to provide information about
    // object sizes at compile time
    // http://gcc.gnu.org/onlinedocs/gcc/Object-Size-Checking.html

    if(expr.arguments().size()!=2)
    {
      err_location(f_op);
      error() << "__builtin_object_size expects two arguments" << eom;
      throw 0;
    }

    make_constant(expr.arguments()[1]);

    mp_integer arg1;

    if(expr.arguments()[1].is_true())
      arg1=1;
    else if(expr.arguments()[1].is_false())
      arg1=0;
    else if(to_integer(expr.arguments()[1], arg1))
    {
      err_location(f_op);
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
      err_location(f_op);
      error() << "__builtin_choose_expr expects three arguments" << eom;
      throw 0;
    }

    expr.arguments()[0].make_typecast(bool_typet());
    make_constant(expr.arguments()[0]);

    if(expr.arguments()[0].is_true())
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
      err_location(f_op);
      error() << "__builtin_constant_p expects one argument" << eom;
      throw 0;
    }

    // try to produce constant
    exprt tmp1=expr.arguments().front();
    simplify(tmp1, *this);

    bool is_constant=false;

    // Need to do some special treatment for string literals,
    // which are (void *)&("lit"[0])
    if(tmp1.id()==ID_typecast &&
       tmp1.operands().size()==1 &&
       tmp1.op0().id()==ID_address_of &&
       tmp1.op0().operands().size()==1 &&
       tmp1.op0().op0().id()==ID_index &&
       tmp1.op0().op0().operands().size()==2 &&
       tmp1.op0().op0().op0().id()==ID_string_constant)
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
      err_location(f_op);
      error() << "__builtin_classify_type expects one argument" << eom;
      throw 0;
    }

    exprt object=expr.arguments()[0];

    // The value doesn't matter at all, we only care about the type.
    // Need to sync with typeclass.h.
    typet type = follow(object.type());

    // use underlying type for bit fields
    if(type.id() == ID_c_bit_field)
      type = to_c_bit_field_type(type).subtype();

    unsigned type_number;

    if(type.id() == ID_bool || type.id() == ID_c_bool)
    {
      // clang returns 4 for _Bool, gcc treats these as 'int'.
      type_number =
        config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::CLANG
          ? 4u
          : 1u;
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
  else if(identifier=="__sync_fetch_and_add" ||
          identifier=="__sync_fetch_and_sub" ||
          identifier=="__sync_fetch_and_or" ||
          identifier=="__sync_fetch_and_and" ||
          identifier=="__sync_fetch_and_xor" ||
          identifier=="__sync_fetch_and_nand" ||
          identifier=="__sync_add_and_fetch" ||
          identifier=="__sync_sub_and_fetch" ||
          identifier=="__sync_or_and_fetch" ||
          identifier=="__sync_and_and_fetch" ||
          identifier=="__sync_xor_and_fetch" ||
          identifier=="__sync_nand_and_fetch" ||
          identifier=="__sync_val_compare_and_swap" ||
          identifier=="__sync_lock_test_and_set" ||
          identifier=="__sync_lock_release")
  {
    // These are polymorphic, see
    // http://gcc.gnu.org/onlinedocs/gcc-4.1.1/gcc/Atomic-Builtins.html

    // adjust return type of function to match pointer subtype
    if(expr.arguments().empty())
    {
      err_location(f_op);
      error() << "__sync_* primitives take as least one argument" << eom;
      throw 0;
    }

    exprt &ptr_arg=expr.arguments().front();

    if(ptr_arg.type().id()!=ID_pointer)
    {
      err_location(f_op);
      error() << "__sync_* primitives take pointer as first argument" << eom;
      throw 0;
    }

    expr.type()=expr.arguments().front().type().subtype();

    return expr;
  }
  else
    return nil_exprt();
}

/// \param type:checked arguments, type-checked function
/// \return type-adjusted function arguments
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
      err_location(expr);
      error() << "not enough function arguments" << eom;
      throw 0;
    }
  }
  else if(parameter_types.size()!=arguments.size())
  {
    err_location(expr);
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

      const typet &type=follow(op.type());
      if(type.id()==ID_array)
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
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "operator `" << expr.id()
            << "' expects one operand" << eom;
    throw 0;
  }

  exprt &operand=expr.op0();

  const typet &o_type=follow(operand.type());

  if(o_type.id()==ID_vector)
  {
    if(is_number(follow(o_type.subtype())))
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

  err_location(expr);
  error() << "operator `" << expr.id()
          << "' not defined for type `"
          << to_string(operand.type()) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_unary_boolean(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error() << "operator `" << expr.id()
            << "' expects one operand" << eom;
    throw 0;
  }

  exprt &operand=expr.op0();

  implicit_typecast_bool(operand);

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
  mp_integer s0, s1;
  if(to_integer(type0.size(), s0))
    return false;
  if(to_integer(type1.size(), s1))
    return false;
  if(s0!=s1)
    return false;

  // compare subtype
  if((type0.subtype().id()==ID_signedbv ||
      type0.subtype().id()==ID_unsignedbv) &&
     (type1.subtype().id()==ID_signedbv ||
      type1.subtype().id()==ID_unsignedbv) &&
     to_bitvector_type(type0.subtype()).get_width()==
     to_bitvector_type(type1.subtype()).get_width())
    return true;

  return type0.subtype()==type1.subtype();
}

void c_typecheck_baset::typecheck_expr_binary_arithmetic(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=follow(op0.type());
  const typet o_type1=follow(op1.type());

  if(o_type0.id()==ID_vector &&
     o_type1.id()==ID_vector)
  {
    if(gcc_vector_types_compatible(
        to_vector_type(o_type0), to_vector_type(o_type1)) &&
       is_number(follow(o_type0.subtype())))
    {
      // Vector arithmetic has fairly strict typing rules, no promotion
      if(o_type0!=o_type1)
        op1.make_typecast(op0.type());
      expr.type()=op0.type();
      return;
    }
  }
  else if(
    o_type0.id() == ID_vector && o_type1.id() != ID_vector &&
    is_number(o_type1))
  {
    // convert op1 to the vector type
    op1.make_typecast(o_type0);
    expr.type() = o_type0;
    return;
  }
  else if(
    o_type0.id() != ID_vector && o_type1.id() == ID_vector &&
    is_number(o_type0))
  {
    // convert op0 to the vector type
    op0.make_typecast(o_type1);
    expr.type() = o_type1;
    return;
  }

  // promote!

  implicit_typecast_arithmetic(op0, op1);

  const typet &type0=follow(op0.type());
  const typet &type1=follow(op1.type());

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
  else if(expr.id()==ID_bitand ||
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitor)
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

  err_location(expr);
  error() << "operator `" << expr.id()
          << "' not defined for types `"
          << to_string(o_type0) << "' and `"
          << to_string(o_type1) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_shifts(shift_exprt &expr)
{
  assert(expr.id()==ID_shl || expr.id()==ID_shr);

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=follow(op0.type());
  const typet o_type1=follow(op1.type());

  if(o_type0.id()==ID_vector &&
     o_type1.id()==ID_vector)
  {
    if(follow(o_type0.subtype())==follow(o_type1.subtype()) &&
       is_number(follow(o_type0.subtype())))
    {
      // {a0, a1, ..., an} >> {b0, b1, ..., bn} ==
      // {a0 >> b0, a1 >> b1, ..., an >> bn}
      // Fairly strict typing rules, no promotion
      expr.type()=op0.type();
      return;
    }
  }

  if(o_type0.id()==ID_vector &&
     is_number(follow(o_type0.subtype())) &&
     is_number(o_type1))
  {
    // {a0, a1, ..., an} >> b == {a0 >> b, a1 >> b, ..., an >> b}
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
      const typet &op0_type=follow(op0.type());

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

  err_location(expr);
  error() << "operator `" << expr.id()
          << "' not defined for types `"
          << to_string(o_type0) << "' and `"
          << to_string(o_type1) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_arithmetic_pointer(const exprt &expr)
{
  const typet &type=expr.type();
  assert(type.id()==ID_pointer);

  typet subtype=type.subtype();

  if(subtype.id()==ID_incomplete_struct)
  {
    err_location(expr);
    error() << "pointer arithmetic with unknown object size" << eom;
    throw 0;
  }
}

void c_typecheck_baset::typecheck_expr_pointer_arithmetic(exprt &expr)
{
  assert(expr.operands().size()==2);

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet &type0=follow(op0.type());
  const typet &type1=follow(op1.type());

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

    const typet &int_op_type=follow(int_op->type());

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

  err_location(expr);
  error() << "operator `" << op_name
          << "' not defined for types `"
          << to_string(type0) << "' and `"
          << to_string(type1) << "'" << eom;
  throw 0;
}

void c_typecheck_baset::typecheck_expr_binary_boolean(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  implicit_typecast_bool(expr.op0());
  implicit_typecast_bool(expr.op1());

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
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    error() << "operator `" << expr.get_statement()
            << "' expects two operands" << eom;
    throw 0;
  }

  const irep_idt &statement=expr.get_statement();

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  {
    const typet &type0=op0.type();

    if(type0.id()==ID_empty)
    {
      err_location(expr);
      error() << "cannot assign void" << eom;
      throw 0;
    }

    if(!op0.get_bool(ID_C_lvalue))
    {
      err_location(expr);
      error() << "assignment error: `" << to_string(op0)
              << "' not an lvalue" << eom;
      throw 0;
    }

    if(type0.get_bool(ID_C_constant))
    {
      err_location(expr);
      error() << "`" << to_string(op0)
              << "' is constant" << eom;
      throw 0;
    }

    // refuse to assign arrays
    if(type0.id()==ID_array ||
       type0.id()==ID_incomplete_array)
    {
      err_location(expr);
      error() << "direct assignments to arrays not permitted" << eom;
      throw 0;
    }
  }

  // Add a cast to the underlying type for bit fields.
  // In particular, sizeof(s.f=1) works for bit fields.
  if(op0.type().id()==ID_c_bit_field)
    op0.make_typecast(op0.type().subtype());

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
    implicit_typecast_arithmetic(op1);

    if(is_number(op1.type()))
    {
      if(statement==ID_assign_shl)
      {
        return;
      }
      else // assign_shr
      {
        // distinguish arithmetic from logical shifts by looking at type

        typet underlying_type=op0.type();

        if(underlying_type.id()==ID_c_enum_tag)
        {
          const typet &c_enum_type=
            follow_tag(to_c_enum_tag_type(underlying_type));
          underlying_type=c_enum_type.subtype();
        }

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
      implicit_typecast_arithmetic(op1);
      if(op1.type().id()==ID_bool ||
         op1.type().id()==ID_c_bool ||
         op1.type().id()==ID_c_enum_tag ||
         op1.type().id()==ID_unsignedbv ||
         op1.type().id()==ID_signedbv)
        return;
    }
    else if(o_type0.id()==ID_c_enum_tag ||
            o_type0.id()==ID_unsignedbv ||
            o_type0.id()==ID_signedbv ||
            o_type0.id()==ID_c_bit_field)
    {
      implicit_typecast(op1, o_type0);
      return;
    }
    else if(o_type0.id()==ID_vector &&
            o_type1.id()==ID_vector)
    {
      // We are willing to do a modest amount of conversion
      if(gcc_vector_types_compatible(
           to_vector_type(o_type0), to_vector_type(o_type1)))
      {
        if(o_type0!=o_type1)
          op1.make_typecast(o_type0);
        return;
      }
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
        if(o_type0!=o_type1)
          op1.make_typecast(o_type0);
        return;
      }
    }
    else if(o_type0.id()==ID_bool ||
            o_type0.id()==ID_c_bool)
    {
      implicit_typecast_arithmetic(op1);
      if(op1.type().id()==ID_bool ||
         op1.type().id()==ID_c_bool ||
         op1.type().id()==ID_c_enum_tag ||
         op1.type().id()==ID_unsignedbv ||
         op1.type().id()==ID_signedbv)
        return;
    }
    else
    {
      implicit_typecast(op1, o_type0);

      if(is_number(op1.type()) ||
         op1.type().id()==ID_bool ||
         op1.type().id()==ID_c_bool ||
         op1.type().id()==ID_c_enum_tag)
        return;
    }
  }

  err_location(expr);
  error() << "assignment `" << statement
          << "' not defined for types `"
          << to_string(o_type0) << "' and `"
          << to_string(o_type1) << "'" << eom;

  throw 0;
}

void c_typecheck_baset::make_constant(exprt &expr)
{
  // Floating-point expressions may require a rounding mode.
  // ISO 9899:1999 F.7.2 says that the default is "round to nearest".
  // Some compilers have command-line options to override.
  const auto rounding_mode =
    from_integer(ieee_floatt::ROUND_TO_EVEN, signed_int_type());
  adjust_float_expressions(expr, rounding_mode);

  simplify(expr, *this);

  if(!expr.is_constant() &&
     expr.id()!=ID_infinity)
  {
    error().source_location=expr.find_source_location();
    error() << "expected constant expression, but got `"
            << to_string(expr) << "'" << eom;
    throw 0;
  }
}

void c_typecheck_baset::make_constant_index(exprt &expr)
{
  make_constant(expr);
  make_index_type(expr);
  simplify(expr, *this);

  if(!expr.is_constant() &&
     expr.id()!=ID_infinity)
  {
    error().source_location=expr.find_source_location();
    error() << "conversion to integer constant failed" << eom;
    throw 0;
  }
}
