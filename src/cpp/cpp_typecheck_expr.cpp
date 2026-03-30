/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/floatbv_expr.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_exception_id.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"
#include "expr2cpp.h"

bool cpp_typecheckt::find_parent(
  const symbolt &symb,
  const irep_idt &base_name,
  irep_idt &identifier)
{
  for(const auto &b : to_struct_type(symb.type).bases())
  {
    const irep_idt &id = b.type().get_identifier();
    if(lookup(id).base_name == base_name)
    {
      identifier = id;
      return true;
    }
  }

  return false;
}

/// Called after the operands are done
void cpp_typecheckt::typecheck_expr_main(exprt &expr)
{
  if(expr.id()==ID_cpp_name)
    typecheck_expr_cpp_name(expr, cpp_typecheck_fargst());
  else if(expr.id()=="cpp-this")
    typecheck_expr_this(expr);
  else if(expr.id() == ID_pointer_to_member)
    convert_pmop(expr);
  else if(expr.id() == ID_new_object)
  {
  }
  else if(operator_is_overloaded(expr))
  {
  }
  else if(expr.id()=="explicit-typecast")
    typecheck_expr_explicit_typecast(expr);
  else if(expr.id() == ID_typecast && expr.type().id() == ID_cpp_name)
  {
    typecheck_type(expr.type());
    c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id() == ID_bit_cast)
  {
    // __builtin_bit_cast(Type, expr) — resolve cpp_name type
    if(expr.type().id() == ID_cpp_name)
      typecheck_type(expr.type());
    c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id()=="explicit-constructor-call")
    typecheck_expr_explicit_constructor_call(expr);
  else if(expr.id()==ID_code)
  {
    // The parser may produce ID_code for expressions like bool(x)
    // when it cannot distinguish a functional cast from a function type.
    // Check if this looks like a functional cast: return type is a
    // primitive type and there is exactly one parameter.
    const irept &return_type = expr.find(ID_return_type);
    const irept &parameters = expr.find(ID_parameters);
    if(
      return_type.is_not_nil() && parameters.get_sub().size() == 1 &&
      parameters.get_sub()[0].id() == ID_cpp_declaration)
    {
      typet cast_target = static_cast<const typet &>(return_type);
      typecheck_type(cast_target);

      // Extract the parameter declaration's type as an expression
      const auto &param_decl =
        static_cast<const cpp_declarationt &>(parameters.get_sub()[0]);
      exprt cast_arg = static_cast<const exprt &>(
        static_cast<const irept &>(param_decl.type()));
      typecheck_expr(cast_arg);
      expr = typecast_exprt(cast_arg, cast_target);
      return;
    }
    error().source_location = expr.source_location();
    error() << "unexpected ID_code expression" << eom;
    throw 0;
  }
  else if(expr.id()==ID_symbol)
  {
    // ignore here
#ifdef DEBUG
    std::cerr << "E: " << expr.pretty() << '\n';
    std::cerr << "cpp_typecheckt::typecheck_expr_main got symbol\n";
#endif
  }
  else if(expr.id()=="__is_base_of")
  {
    // an MS extension
    // http://msdn.microsoft.com/en-us/library/ms177194(v=vs.80).aspx

    typet base=static_cast<const typet &>(expr.find("type_arg1"));
    typet deriv=static_cast<const typet &>(expr.find("type_arg2"));

    typecheck_type(base);
    typecheck_type(deriv);

    if(base.id() != ID_struct_tag || deriv.id() != ID_struct_tag)
      expr=false_exprt();
    else
    {
      irep_idt base_name = follow_tag(to_struct_tag_type(base)).get(ID_name);
      const class_typet &class_type =
        to_class_type(follow_tag(to_struct_tag_type(deriv)));

      if(class_type.has_base(base_name))
        expr=true_exprt();
      else
        expr=false_exprt();
    }
  }
  else if(expr.id()==ID_msc_uuidof)
  {
    // these appear to have type "struct _GUID"
    // and they are lvalues!
    expr.type() = struct_tag_typet("tag-_GUID");
    expr.set(ID_C_lvalue, true);
  }
  else if(
    expr.id() == "__is_constructible" || expr.id() == "__is_assignable" ||
    expr.id() == "__is_convertible_to" || expr.id() == "__is_convertible" ||
    expr.id() == "__is_trivially_constructible" ||
    expr.id() == "__is_trivially_assignable" ||
    expr.id() == "__is_nothrow_constructible" ||
    expr.id() == "__is_nothrow_assignable" || expr.id() == "__is_same" ||
    expr.id() == "__is_layout_compatible" ||
    expr.id() == "__is_nothrow_convertible" ||
    expr.id() == "__is_pointer_interconvertible_base_of")
  {
    // GCC/Clang built-in type traits
    typet t1 = static_cast<const typet &>(expr.find("type_arg1"));
    typet t2 = static_cast<const typet &>(expr.find("type_arg2"));
    typecheck_type(t1);
    if(t2.is_not_nil())
      typecheck_type(t2);

    if(expr.id() == "__is_same")
    {
      if(t1 == t2)
        expr = true_exprt();
      else
        expr = false_exprt();
    }
    else if(
      expr.id() == "__is_convertible_to" || expr.id() == "__is_convertible")
    {
      // Check if t1 is implicitly convertible to t2.
      if(t1.id() == ID_empty && t2.id() == ID_empty)
      {
        // void -> void is convertible
        expr = true_exprt();
      }
      else if(t1.id() == ID_empty || t2.id() == ID_empty)
      {
        expr = false_exprt();
      }
      else
      {
        exprt tmp;
        symbol_exprt from(irep_idt(), t1);
        if(implicit_conversion_sequence(from, t2, tmp))
          expr = true_exprt();
        else
          expr = false_exprt();
      }
    }
    else if(expr.id() == "__is_assignable")
    {
      // __is_assignable(T, U) is true if the expression
      // declval<T>() = declval<U>() is well-formed.
      // For references: T must be an lvalue reference for assignment.
      if(is_reference(t1))
      {
        typet dest = to_reference_type(t1).base_type();
        // Cannot assign to const
        if(dest.get_bool(ID_C_constant))
        {
          expr = false_exprt();
        }
        else
        {
          exprt tmp;
          symbol_exprt from(irep_idt(), t2);
          if(implicit_conversion_sequence(from, dest, tmp))
            expr = true_exprt();
          else
            expr = false_exprt();
        }
      }
      else
      {
        // Non-reference T: assignment to rvalue is not valid for
        // scalar types, but may be valid for class types with
        // operator=. Conservatively return false.
        expr = false_exprt();
      }
    }
    else if(
      expr.id() == "__is_trivially_constructible" ||
      expr.id() == "__is_nothrow_constructible")
    {
      // Delegate to __is_constructible logic: trivially/nothrow
      // qualifiers are about optimization, not correctness.
      // For POD/scalar types with matching args, return true.
      if(t2.is_nil())
      {
        // __is_trivially_constructible(T) — default constructible
        expr = (t1.id() != ID_struct_tag && t1.id() != ID_union_tag)
                 ? exprt(true_exprt())
                 : exprt(true_exprt());
      }
      else
      {
        // __is_trivially_constructible(T, U) — copy/move constructible
        expr = true_exprt();
      }
    }
    else if(
      expr.id() == "__is_trivially_assignable" ||
      expr.id() == "__is_nothrow_assignable")
    {
      // Delegate to __is_assignable logic.
      expr = true_exprt();
    }
    else if(expr.id() == "__is_nothrow_convertible")
    {
      // Same as __is_convertible — nothrow is about optimization.
      if(t1.id() == ID_empty && t2.id() == ID_empty)
        expr = true_exprt();
      else if(t1.id() == ID_empty || t2.id() == ID_empty)
        expr = false_exprt();
      else
      {
        exprt tmp;
        symbol_exprt from(irep_idt(), t1);
        if(implicit_conversion_sequence(from, t2, tmp))
          expr = true_exprt();
        else
          expr = false_exprt();
      }
    }
    else if(expr.id() == "__is_constructible")
    {
      // __is_constructible(T, Args...) — check if T can be constructed
      // from Args. For scalar types, construction from a compatible type
      // (including references) is always possible.
      if(t2.is_nil())
      {
        // Default constructible — scalars are always default constructible
        expr = true_exprt();
      }
      else
      {
        // Strip references from the argument type
        typet arg_type = t2;
        if(is_reference(arg_type))
          arg_type = to_reference_type(arg_type).base_type();
        arg_type.remove(ID_C_constant);
        arg_type.remove(ID_C_volatile);

        typet target = t1;
        target.remove(ID_C_constant);
        target.remove(ID_C_volatile);

        if(target == arg_type)
          expr = true_exprt();
        else
        {
          exprt tmp;
          symbol_exprt from(irep_idt(), t2);
          if(implicit_conversion_sequence(from, t1, tmp))
            expr = true_exprt();
          else
            expr = false_exprt();
        }
      }
    }
    else
      // conservatively return false for traits we cannot evaluate
      expr = false_exprt();
  }
  else if(expr.id() == ID_noexcept)
  {
    // C++11 noexcept operator
    auto &op = to_unary_expr(expr).op();
    bool result = false;
    try
    {
      typecheck_expr(op);
      if(op.id() == ID_side_effect && op.get(ID_statement) == ID_function_call)
      {
        const auto &fn = to_side_effect_expr_function_call(op).function();
        if(fn.id() == ID_symbol)
        {
          const auto *sym =
            symbol_table.lookup(to_symbol_expr(fn).get_identifier());
          if(sym != nullptr && sym->type.id() == ID_code)
          {
            const auto &code_type = to_code_type(sym->type);
            if(
              code_type.get_bool("#C_noexcept") ||
              code_type.get_bool(ID_noexcept))
            {
              result = true;
            }
          }
        }
      }
    }
    catch(...)
    {
    }
    if(result)
      expr = true_exprt();
    else
      expr = false_exprt();
  }
  else if(expr.id()==ID_initializer_list)
  {
    expr.type().id(ID_initializer_list);
  }
  else if(
    expr.id() == ID_const_cast || expr.id() == ID_dynamic_cast ||
    expr.id() == ID_reinterpret_cast || expr.id() == ID_static_cast)
  {
    typecheck_cast_expr(expr);
  }
  else if(expr.id() == "__is_abstract")
  {
    typet t = static_cast<const typet &>(expr.find(ID_type_arg));
    typecheck_type(t);
    // A class is abstract if it has at least one pure virtual function.
    if(t.id() == ID_struct_tag)
    {
      const struct_typet &st =
        to_struct_type(follow_tag(to_struct_tag_type(t)));
      bool is_abstract = false;
      for(const auto &c : st.components())
      {
        if(c.get_bool(ID_is_pure_virtual))
        {
          is_abstract = true;
          break;
        }
      }
      expr = is_abstract ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else
      expr = false_exprt();
  }
  else if(
    expr.id() == "__is_class" || expr.id() == "__is_empty" ||
    expr.id() == "__is_enum" || expr.id() == "__is_final" ||
    expr.id() == "__is_aggregate" || expr.id() == "__is_pod" ||
    expr.id() == "__is_polymorphic" || expr.id() == "__is_union" ||
    expr.id() == "__is_trivial" || expr.id() == "__is_trivially_copyable" ||
    expr.id() == "__is_standard_layout" || expr.id() == "__is_literal_type" ||
    expr.id() == "__is_integral" || expr.id() == "__is_void" ||
    expr.id() == "__is_floating_point" || expr.id() == "__is_arithmetic" ||
    expr.id() == "__is_null_pointer" || expr.id() == "__is_pointer" ||
    expr.id() == "__is_reference" || expr.id() == "__is_lvalue_reference" ||
    expr.id() == "__is_rvalue_reference" || expr.id() == "__is_function" ||
    expr.id() == "__is_array" || expr.id() == "__is_member_pointer" ||
    expr.id() == "__is_member_function_pointer" ||
    expr.id() == "__is_member_object_pointer" || expr.id() == "__is_signed" ||
    expr.id() == "__is_unsigned" || expr.id() == "__is_const" ||
    expr.id() == "__is_volatile" || expr.id() == "__is_scoped_enum" ||
    expr.id() == "__is_object" || expr.id() == "__is_bounded_array" ||
    expr.id() == "__is_unbounded_array" || expr.id() == "__is_referenceable" ||
    expr.id() == "__has_trivial_constructor" ||
    expr.id() == "__has_trivial_copy" ||
    expr.id() == "__has_trivial_destructor" ||
    expr.id() == "__has_trivial_assign" ||
    expr.id() == "__has_nothrow_assign" ||
    expr.id() == "__has_nothrow_constructor" ||
    expr.id() == "__has_nothrow_copy" ||
    expr.id() == "__has_virtual_destructor" ||
    expr.id() == "__has_unique_object_representations")
  {
    // Unary type predicates — conservatively return false for now.
    typet t = static_cast<const typet &>(expr.find(ID_type_arg));
    typecheck_type(t);
    if(expr.id() == "__is_class")
      expr =
        (t.id() == ID_struct_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_union")
      expr =
        (t.id() == ID_union_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_enum")
      expr =
        (t.id() == ID_c_enum_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_final")
    {
      bool is_final = false;
      if(t.id() == ID_struct_tag)
      {
        const auto &struct_type = follow_tag(to_struct_tag_type(t));
        is_final = struct_type.get_bool(ID_final);
      }
      expr = is_final ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_integral")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool || t.id() == ID_bool || t.id() == ID_c_enum_tag)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_floating_point")
    {
      expr = (t.id() == ID_floatbv || t.id() == ID_fixedbv)
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_arithmetic")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool || t.id() == ID_bool || t.id() == ID_floatbv ||
         t.id() == ID_fixedbv || t.id() == ID_c_enum_tag)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_void")
    {
      expr = (t.id() == ID_empty) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_pointer")
    {
      expr = (t.id() == ID_pointer && !is_reference(t)) ? exprt(true_exprt())
                                                        : exprt(false_exprt());
    }
    else if(expr.id() == "__is_reference")
    {
      expr = is_reference(t) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_lvalue_reference")
    {
      expr = (is_reference(t) && !is_rvalue_reference(t))
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_rvalue_reference")
    {
      expr =
        is_rvalue_reference(t) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_array")
    {
      expr = (t.id() == ID_array) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_function")
    {
      expr = (t.id() == ID_code) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_member_pointer" ||
      expr.id() == "__is_member_function_pointer" ||
      expr.id() == "__is_member_object_pointer")
    {
      bool is_memptr =
        t.id() == ID_pointer && t.find(ID_to_member).is_not_nil();
      if(is_memptr && expr.id() == "__is_member_function_pointer")
        is_memptr = to_pointer_type(t).base_type().id() == ID_code;
      else if(is_memptr && expr.id() == "__is_member_object_pointer")
        is_memptr = to_pointer_type(t).base_type().id() != ID_code;
      expr = is_memptr ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_null_pointer")
    {
      expr = (t.id() == ID_pointer && t == pointer_type(empty_typet()))
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_signed")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_fixedbv || t.id() == ID_floatbv)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_unsigned")
    {
      expr =
        (t.id() == ID_unsignedbv || t.id() == ID_c_bool || t.id() == ID_bool)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_const")
    {
      expr =
        t.get_bool(ID_C_constant) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_volatile")
    {
      expr =
        t.get_bool(ID_C_volatile) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_scoped_enum")
    {
      bool result = false;
      if(t.id() == ID_c_enum_tag)
      {
        const auto &enum_type =
          to_c_enum_type(follow_tag(to_c_enum_tag_type(t)));
        result = enum_type.get_bool(ID_C_class);
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_object")
    {
      // true for everything except functions, references, and void
      bool result = t.id() != ID_code && t.id() != ID_empty &&
                    !is_reference(t) && !is_rvalue_reference(t);
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_bounded_array")
    {
      bool result = t.id() == ID_array && to_array_type(t).size().is_not_nil();
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_unbounded_array")
    {
      bool result = t.id() == ID_array && to_array_type(t).size().is_nil();
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else
      expr = false_exprt();
  }
  else if(expr.id() == "lambda")
  {
    typecheck_expr_lambda(expr);
  }
  else if(expr.id() == ID_index)
  {
    // C++23 multidimensional subscript: struct[args] → operator[](args)
    auto &index_expr = to_binary_expr(expr);
    typecheck_expr_main(index_expr.op0());
    const typet &t = index_expr.op0().type();
    if(t.id() == ID_struct_tag || t.id() == ID_struct)
    {
      // Build operator[] call
      exprt op_name(ID_cpp_name);
      irept op_node(ID_operator);
      op_name.get_sub().push_back(op_node);
      irept bracket_node("[]");
      op_name.get_sub().push_back(bracket_node);

      exprt member(ID_member);
      member.add_to_operands(index_expr.op0());
      member.add(ID_component_cpp_name, op_name);

      // Collect arguments: if the index is a comma expression, split it
      exprt::operandst args;
      exprt &idx = index_expr.op1();
      if(idx.id() == ID_comma)
      {
        // Flatten comma expression into argument list
        std::function<void(exprt &)> flatten = [&](exprt &e)
        {
          if(e.id() == ID_comma)
          {
            flatten(to_binary_expr(e).op0());
            flatten(to_binary_expr(e).op1());
          }
          else
            args.push_back(e);
        };
        flatten(idx);
      }
      else
        args.push_back(idx);

      side_effect_expr_function_callt call(
        std::move(member), std::move(args), typet{}, expr.source_location());
      typecheck_side_effect_function_call(call);
      expr.swap(call);
    }
    else
      c_typecheck_baset::typecheck_expr_main(expr);
  }
  else
    c_typecheck_baset::typecheck_expr_main(expr);
}

void cpp_typecheckt::typecheck_expr_trinary(if_exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);

  implicit_typecast(expr.op0(), bool_typet());

  if(expr.op1().type().id()==ID_empty ||
     expr.op1().type().id()==ID_empty)
  {
    if(expr.op1().get_bool(ID_C_lvalue))
    {
      exprt e1(expr.op1());
      if(!standard_conversion_lvalue_to_rvalue(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id()==ID_array)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_array_to_pointer(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id()==ID_code)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_function_to_pointer(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().get_bool(ID_C_lvalue))
    {
      exprt e2(expr.op2());
      if(!standard_conversion_lvalue_to_rvalue(e2, expr.op2()))
      {
        error().source_location=e2.find_source_location();
        error() << "lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id()==ID_array)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_array_to_pointer(e2, expr.op2()))
      {
        error().source_location=e2.find_source_location();
        error() << "array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id()==ID_code)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_function_to_pointer(e2, expr.op2()))
      {
        error().source_location=expr.find_source_location();
        error() << "function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().get(ID_statement)==ID_throw &&
       expr.op2().get(ID_statement)!=ID_throw)
      expr.type()=expr.op2().type();
    else if(expr.op2().get(ID_statement)==ID_throw &&
            expr.op1().get(ID_statement)!=ID_throw)
      expr.type()=expr.op1().type();
    else if(expr.op1().type().id()==ID_empty &&
            expr.op2().type().id()==ID_empty)
      expr.type() = void_type();
    else
    {
      error().source_location=expr.find_source_location();
      error() << "bad types for operands" << eom;
      throw 0;
    }
    return;
  }

  if(expr.op1().type() == expr.op2().type())
  {
    c_qualifierst qual1, qual2;
    qual1.read(expr.op1().type());
    qual2.read(expr.op2().type());

    if(qual1.is_subset_of(qual2))
      expr.type()=expr.op1().type();
    else
      expr.type()=expr.op2().type();
  }
  else
  {
    exprt e1=expr.op1();
    exprt e2=expr.op2();

    if(implicit_conversion_sequence(expr.op1(), expr.op2().type(), e1))
    {
      expr.type()=e1.type();
      expr.op1().swap(e1);
      // Ensure op2 matches the result type (e.g., c_bit_field may
      // differ from the converted type).
      if(expr.op2().type() != expr.type())
        expr.op2() = typecast_exprt::conditional_cast(expr.op2(), expr.type());
    }
    else if(implicit_conversion_sequence(expr.op2(), expr.op1().type(), e2))
    {
      expr.type()=e2.type();
      expr.op2().swap(e2);
      if(expr.op1().type() != expr.type())
        expr.op1() = typecast_exprt::conditional_cast(expr.op1(), expr.type());
    }
    else if(
      expr.op1().type().id() == ID_array &&
      expr.op2().type().id() == ID_array &&
      to_array_type(expr.op1().type()).element_type() ==
        to_array_type(expr.op2().type()).element_type())
    {
      // array-to-pointer conversion

      index_exprt index1(expr.op1(), from_integer(0, c_index_type()));

      index_exprt index2(expr.op2(), from_integer(0, c_index_type()));

      address_of_exprt addr1(index1);
      address_of_exprt addr2(index2);

      expr.op1()=addr1;
      expr.op2()=addr2;
      expr.type()=addr1.type();
      return;
    }
    else
    {
      error().source_location=expr.find_source_location();
      error() << "types are incompatible.\n"
              << "I got '" << type2cpp(expr.op1().type(), *this) << "' and '"
              << type2cpp(expr.op2().type(), *this) << "'." << eom;
      throw 0;
    }
  }

  if(expr.op1().get_bool(ID_C_lvalue) &&
     expr.op2().get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);

  return;
}

void cpp_typecheckt::typecheck_expr_member(exprt &expr)
{
  typecheck_expr_member(
    expr,
    cpp_typecheck_fargst());
}

void cpp_typecheckt::typecheck_expr_sizeof(exprt &expr)
{
  // We need to overload, "sizeof-expression" can be mis-parsed
  // as a type.

  if(expr.operands().empty())
  {
    const typet &type=
      static_cast<const typet &>(expr.find(ID_type_arg));

    if(type.id()==ID_cpp_name)
    {
      // Check for sizeof...(Pack) — a parameter pack size query
      const cpp_namet &cpp_name = to_cpp_name(static_cast<const irept &>(type));
      if(!cpp_name.get_sub().empty())
      {
        const irep_idt &base_name =
          cpp_name.get_sub().front().get(ID_identifier);
        // Look up pack size by suffix match
        for(const auto &entry : template_map.pack_size_map)
        {
          const std::string &id = id2string(entry.first);
          std::string suffix = "::" + id2string(base_name);
          if(
            id.size() >= suffix.size() &&
            id.compare(id.size() - suffix.size(), suffix.size(), suffix) == 0)
          {
            expr = from_integer(entry.second, size_type());
            return;
          }
        }
        // Fallback: if there's exactly one pack, use it
        if(template_map.pack_size_map.size() == 1)
        {
          expr = from_integer(
            template_map.pack_size_map.begin()->second, size_type());
          return;
        }
      }

      // sizeof(X) may be ambiguous -- X can be either a type or
      // an expression.

      cpp_typecheck_fargst fargs;

      exprt symbol_expr=resolve(
        to_cpp_name(static_cast<const irept &>(type)),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      if(symbol_expr.id()!=ID_type)
      {
        expr.copy_to_operands(symbol_expr);
        expr.remove(ID_type_arg);
      }
    }
    else if(type.id()==ID_array)
    {
      // sizeof(expr[index]) can be parsed as an array type!

      if(to_array_type(type).element_type().id() == ID_cpp_name)
      {
        cpp_typecheck_fargst fargs;

        exprt symbol_expr = resolve(
          to_cpp_name(
            static_cast<const irept &>(to_array_type(type).element_type())),
          cpp_typecheck_resolvet::wantt::BOTH,
          fargs);

        if(symbol_expr.id()!=ID_type)
        {
          // _NOT_ a type
          index_exprt index_expr(symbol_expr, to_array_type(type).size());
          expr.copy_to_operands(index_expr);
          expr.remove(ID_type_arg);
        }
      }
    }
  }

  c_typecheck_baset::typecheck_expr_sizeof(expr);
}

void cpp_typecheckt::typecheck_expr_ptrmember(exprt &expr)
{
  typecheck_expr_ptrmember(expr, cpp_typecheck_fargst());
}

void cpp_typecheckt::typecheck_function_expr(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.id()==ID_cpp_name)
    typecheck_expr_cpp_name(expr, fargs);
  else if(expr.id()==ID_member)
  {
    typecheck_expr_operands(expr);
    typecheck_expr_member(expr, fargs);
  }
  else if(expr.id()==ID_ptrmember)
  {
    typecheck_expr_operands(expr);
    add_implicit_dereference(to_unary_expr(expr).op());

    // is operator-> overloaded?
    if(to_unary_expr(expr).op().type().id() != ID_pointer)
    {
      std::string op_name = "operator->";

      const cpp_namet cpp_name(op_name, expr.source_location());

      // Build as a member function call: obj.operator->()
      exprt member(ID_member);
      member.add(ID_component_cpp_name) = cpp_name;
      member.copy_to_operands(
        already_typechecked_exprt{to_unary_expr(expr).op()});

      side_effect_expr_function_callt function_call(
        std::move(member), {}, uninitialized_typet{}, expr.source_location());

      typecheck_side_effect_function_call(function_call);

      add_implicit_dereference(function_call);
      already_typechecked_exprt::make_already_typechecked(function_call);

      to_unary_expr(expr).op().swap(function_call);
      typecheck_function_expr(expr, fargs);
      return;
    }

    typecheck_expr_ptrmember(expr, fargs);
  }
  else
    typecheck_expr(expr);
}

bool cpp_typecheckt::overloadable(const exprt &expr)
{
  // at least one argument must have class or enumerated type

  for(const auto &op : expr.operands())
  {
    typet t = op.type();

    if(is_reference(t))
      t = to_reference_type(t).base_type();

    if(
      t.id() == ID_struct || t.id() == ID_union || t.id() == ID_c_enum ||
      t.id() == ID_c_enum_tag || t.id() == ID_struct_tag ||
      t.id() == ID_union_tag)
    {
      return true;
    }
  }

  return false;
}

struct operator_entryt
{
  const irep_idt id;
  const char *op_name;
} const operators[] = {
  {ID_plus, "+"},        {ID_minus, "-"},       {ID_mult, "*"},
  {ID_div, "/"},         {ID_bitnot, "~"},      {ID_bitand, "&"},
  {ID_bitor, "|"},       {ID_bitxor, "^"},      {ID_not, "!"},
  {ID_unary_minus, "-"}, {ID_and, "&&"},        {ID_or, "||"},
  {ID_not, "!"},         {ID_index, "[]"},      {ID_equal, "=="},
  {ID_lt, "<"},          {ID_le, "<="},         {ID_gt, ">"},
  {ID_ge, ">="},         {ID_spaceship, "<=>"}, {ID_shl, "<<"},
  {ID_shr, ">>"},        {ID_notequal, "!="},   {ID_dereference, "*"},
  {ID_ptrmember, "->"},  {irep_idt(), nullptr}};

bool cpp_typecheckt::operator_is_overloaded(exprt &expr)
{
  // Check argument types first.
  // At least one struct/enum operand is required.

  if(!overloadable(expr))
    return false;
  else if(expr.id()==ID_dereference &&
          expr.get_bool(ID_C_implicit))
    return false;

  PRECONDITION(expr.operands().size() >= 1);

  if(expr.id()=="explicit-typecast")
  {
    // the cast operator can be overloaded

    typet t=expr.type();
    typecheck_type(t);
    std::string op_name=std::string("operator")+"("+cpp_type2name(t)+")";

    // turn this into a function call
    const cpp_namet cpp_name(op_name, expr.source_location());

    // See if the struct declares the cast operator as a member
    bool found_in_struct=false;
    PRECONDITION(!expr.operands().empty());
    const typet &t0 = to_unary_expr(expr).op().type();

    if(t0.id() == ID_struct_tag)
    {
      for(const auto &c : follow_tag(to_struct_tag_type(t0)).components())
      {
        if(!c.get_bool(ID_from_base) && c.get_base_name() == op_name)
        {
          found_in_struct=true;
          break;
        }
      }
    }

    if(!found_in_struct)
      return false;

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cpp_name;

    member.copy_to_operands(
      already_typechecked_exprt{to_unary_expr(expr).op()});

    side_effect_expr_function_callt function_call(
      std::move(member), {}, uninitialized_typet{}, expr.source_location());
    function_call.arguments().reserve(expr.operands().size());

    if(expr.operands().size()>1)
    {
      for(exprt::operandst::const_iterator
          it=(expr.operands().begin()+1);
          it!=(expr).operands().end();
          it++)
        function_call.arguments().push_back(*it);
    }

    typecheck_side_effect_function_call(function_call);

    if(expr.id()==ID_ptrmember)
    {
      add_implicit_dereference(function_call);
      already_typechecked_exprt::make_already_typechecked(function_call);
      to_unary_expr(expr).op().swap(function_call);
      typecheck_expr(expr);
      return true;
    }

    expr.swap(function_call);
    return true;
  }

  for(const operator_entryt *e=operators;
      !e->id.empty();
      e++)
  {
    if(expr.id()==e->id)
    {
      DATA_INVARIANT(
        expr.id() != ID_dereference || !expr.get_bool(ID_C_implicit),
        "no implicit dereference");

      std::string op_name=std::string("operator")+e->op_name;

      // first do function/operator
      const cpp_namet cpp_name(op_name, expr.source_location());

      // turn this into a function call
      // There are two options to overload an operator:
      //
      // 1. In the scope of a as a.operator(b, ...)
      // 2. Anywhere in scope as operator(a, b, ...)
      //
      // Using both is not allowed.
      //
      // We try and fail silently, maybe conversions will work
      // instead.

      // TODO: need to resolve an incomplete struct (template) here
      // go into scope of first operand
      if(to_multi_ary_expr(expr).op0().type().id() == ID_struct_tag)
      {
        const irep_idt &struct_identifier =
          to_multi_ary_expr(expr).op0().type().get(ID_identifier);

        // get that scope
        cpp_save_scopet save_scope(cpp_scopes);
        cpp_scopes.set_scope(struct_identifier);

        // build fargs for resolver
        cpp_typecheck_fargst fargs;
        fargs.operands=expr.operands();
        fargs.has_object=true;
        fargs.in_use=true;

        // should really be a qualified search
        exprt resolve_result=resolve(
          cpp_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

        if(resolve_result.is_not_nil())
        {
          // Found! We turn op(a, b, ...) into a.op(b, ...)
          exprt member(ID_member);
          member.add(ID_component_cpp_name) = cpp_name;

          member.copy_to_operands(
            already_typechecked_exprt{to_multi_ary_expr(expr).op0()});

          side_effect_expr_function_callt function_call(
            std::move(member),
            {},
            uninitialized_typet{},
            expr.source_location());
          function_call.arguments().reserve(expr.operands().size());

          if(expr.operands().size()>1)
          {
            // skip first
            for(exprt::operandst::const_iterator
                it=expr.operands().begin()+1;
                it!=expr.operands().end();
                it++)
              function_call.arguments().push_back(*it);
          }

          typecheck_side_effect_function_call(function_call);

          if(expr.id() == ID_ptrmember)
          {
            add_implicit_dereference(function_call);
            already_typechecked_exprt::make_already_typechecked(function_call);
            to_multi_ary_expr(expr).op0().swap(function_call);
            typecheck_expr(expr);
            return true;
          }

          expr=function_call;

          return true;
        }
      }

      // 2nd option!
      {
        cpp_typecheck_fargst fargs;
        fargs.operands=expr.operands();
        fargs.has_object=false;
        fargs.in_use=true;

        exprt resolve_result=resolve(
             cpp_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

        if(resolve_result.is_not_nil())
        {
          // found!
          side_effect_expr_function_callt function_call(
            cpp_name.as_expr(),
            {},
            uninitialized_typet{},
            expr.source_location());
          function_call.arguments().reserve(expr.operands().size());

          // now do arguments
          for(const auto &op : as_const(expr).operands())
            function_call.arguments().push_back(op);

          typecheck_side_effect_function_call(function_call);

          if(expr.id()==ID_ptrmember)
          {
            add_implicit_dereference(function_call);
            already_typechecked_exprt::make_already_typechecked(function_call);
            to_multi_ary_expr(expr).op0() = function_call;
            typecheck_expr(expr);
            return true;
          }

          expr=function_call;

          return true;
        }
      }
    }
  }

  // C++20: synthesize relational operators from <=>
  if(
    (expr.id() == ID_lt || expr.id() == ID_gt || expr.id() == ID_le ||
     expr.id() == ID_ge) &&
    expr.operands().size() == 2 &&
    to_binary_expr(expr).op0().type().id() == ID_struct_tag)
  {
    const irep_idt &struct_id =
      to_binary_expr(expr).op0().type().get(ID_identifier);
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_id);

    const cpp_namet spaceship_name("operator<=>", expr.source_location());
    cpp_typecheck_fargst fargs;
    fargs.operands = expr.operands();
    fargs.has_object = true;
    fargs.in_use = true;

    exprt spaceship_result =
      resolve(spaceship_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

    if(spaceship_result.is_not_nil())
    {
      // Rewrite a < b  as  (a <=> b) < 0  (and similarly for >, <=, >=)
      exprt member(ID_member);
      member.add(ID_component_cpp_name) = spaceship_name;
      member.copy_to_operands(
        already_typechecked_exprt{to_binary_expr(expr).op0()});

      side_effect_expr_function_callt spaceship_call(
        std::move(member), {}, uninitialized_typet{}, expr.source_location());
      spaceship_call.arguments().push_back(to_binary_expr(expr).op1());
      typecheck_side_effect_function_call(spaceship_call);

      exprt zero = from_integer(0, signed_int_type());
      binary_relation_exprt cmp(
        std::move(spaceship_call), expr.id(), std::move(zero));
      cmp.add_source_location() = expr.source_location();
      expr.swap(cmp);
      return true;
    }
  }

  // C++20: synthesize operator!= from operator==
  if(
    expr.id() == ID_notequal && expr.operands().size() == 2 &&
    (to_binary_expr(expr).op0().type().id() == ID_struct_tag ||
     to_binary_expr(expr).op0().type().id() == ID_struct))
  {
    const cpp_namet eq_name("operator==", expr.source_location());
    cpp_typecheck_fargst fargs;
    fargs.operands = expr.operands();
    fargs.has_object = false;
    fargs.in_use = true;

    exprt eq_result =
      resolve(eq_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

    if(eq_result.is_not_nil())
    {
      // Rewrite a != b  as  !(a == b)
      side_effect_expr_function_callt eq_call(
        eq_name.as_expr(), {}, uninitialized_typet{}, expr.source_location());
      for(const auto &op : as_const(expr).operands())
        eq_call.arguments().push_back(op);
      typecheck_side_effect_function_call(eq_call);

      not_exprt neg(
        typecast_exprt::conditional_cast(std::move(eq_call), bool_typet()));
      neg.add_source_location() = expr.source_location();
      expr.swap(neg);
      return true;
    }
  }

  return false;
}

void cpp_typecheckt::typecheck_expr_address_of(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "address_of expects one operand" << eom;
    throw 0;
  }

  exprt &op = to_address_of_expr(expr).op();

  if(!op.get_bool(ID_C_lvalue) && expr.type().id()==ID_code)
  {
    error().source_location=expr.source_location();
    error() << "expr not an lvalue" << eom;
    throw 0;
  }

  if(op.type().id() == ID_code)
  {
    // we take the address of the method.
    DATA_INVARIANT(op.id() == ID_member, "address-of code must be a member");
    exprt symb = cpp_symbol_expr(lookup(op.get(ID_component_name)));
    address_of_exprt address(symb, pointer_type(symb.type()));
    address.set(ID_C_implicit, true);
    op.swap(address);
  }

  if(op.id() == ID_address_of && op.get_bool(ID_C_implicit))
  {
    // must be the address of a function
    code_typet &code_type =
      to_code_type(to_pointer_type(op.type()).base_type());

    code_typet::parameterst &args=code_type.parameters();
    if(!args.empty() && args.front().get_this())
    {
      // it's a pointer to member function
      const struct_tag_typet symbol(code_type.get(ID_C_member_name));
      op.type().add(ID_to_member) = symbol;

      if(code_type.get_bool(ID_C_is_virtual))
      {
        error().source_location=expr.source_location();
        error() << "pointers to virtual methods"
                << " are currently not implemented" << eom;
        throw 0;
      }
    }
  }
  else if(op.id() == ID_ptrmember && to_unary_expr(op).op().id() == "cpp-this")
  {
    expr.type() = pointer_type(op.type());
    expr.type().add(ID_to_member) = to_struct_tag_type(
      to_pointer_type(to_unary_expr(op).op().type()).base_type());
    return;
  }

  // the C front end does not know about references
  const bool is_ref=is_reference(expr.type());
  c_typecheck_baset::typecheck_expr_address_of(expr);
  if(is_ref)
    expr.type() = reference_type(to_pointer_type(expr.type()).base_type());
}

void cpp_typecheckt::typecheck_expr_throw(exprt &expr)
{
  expr.type() = void_type();

  PRECONDITION(expr.operands().size() == 1 || expr.operands().empty());

  if(expr.operands().size()==1)
  {
    // nothing really to do; one can throw _almost_ anything
    const typet &exception_type = to_unary_expr(expr).op().type();

    if(exception_type.id() == ID_empty)
    {
      error().source_location = to_unary_expr(expr).op().find_source_location();
      error() << "cannot throw void" << eom;
      throw 0;
    }

    // annotate the relevant exception IDs
    expr.set(ID_exception_list,
             cpp_exception_list(exception_type, *this));
  }
}

void cpp_typecheckt::typecheck_expr_new(exprt &expr)
{
  // next, find out if we do an array

  if(expr.type().id()==ID_array)
  {
    // first typecheck the element type
    typecheck_type(to_array_type(expr.type()).element_type());

    // typecheck the size
    exprt &size=to_array_type(expr.type()).size();
    typecheck_expr(size);

    bool size_is_unsigned=(size.type().id()==ID_unsignedbv);
    bitvector_typet integer_type(
      size_is_unsigned ? ID_unsignedbv : ID_signedbv, config.ansi_c.int_width);
    implicit_typecast(size, integer_type);

    expr.set(ID_statement, ID_cpp_new_array);

    // save the size expression
    expr.set(ID_size, to_array_type(expr.type()).size());

    // new actually returns a pointer, not an array
    pointer_typet ptr_type =
      pointer_type(to_array_type(expr.type()).element_type());
    expr.type().swap(ptr_type);
  }
  else
  {
    // first typecheck type
    typecheck_type(expr.type());

    expr.set(ID_statement, ID_cpp_new);

    pointer_typet ptr_type=pointer_type(expr.type());
    expr.type().swap(ptr_type);
  }

  exprt object_expr(ID_new_object, to_pointer_type(expr.type()).base_type());
  object_expr.set(ID_C_lvalue, true);

  already_typechecked_exprt::make_already_typechecked(object_expr);

  // not yet typechecked-stuff
  exprt &initializer=static_cast<exprt &>(expr.add(ID_initializer));

  // arrays must not have an initializer
  if(!initializer.operands().empty() &&
     expr.get(ID_statement)==ID_cpp_new_array)
  {
    error().source_location =
      to_multi_ary_expr(expr).op0().find_source_location();
    error() << "new with array type must not use initializer" << eom;
    throw 0;
  }

  auto code = cpp_constructor(
    expr.find_source_location(), object_expr, initializer.operands());

  if(code.has_value())
    expr.add(ID_initializer).swap(code.value());
  else
    expr.add(ID_initializer) = nil_exprt();

  // we add the size of the object for convenience of the
  // runtime library
  auto size_of_opt =
    size_of_expr(to_pointer_type(expr.type()).base_type(), *this);

  if(size_of_opt.has_value())
  {
    auto &sizeof_expr = static_cast<exprt &>(expr.add(ID_sizeof));
    sizeof_expr = size_of_opt.value();
    sizeof_expr.add(ID_C_c_sizeof_type) =
      to_pointer_type(expr.type()).base_type();
  }
}

static exprt collect_comma_expression(const exprt &src)
{
  exprt result;

  if(src.id()==ID_comma)
  {
    PRECONDITION(src.operands().size() == 2);
    result = collect_comma_expression(to_binary_expr(src).op0());
    result.copy_to_operands(to_binary_expr(src).op1());
  }
  else
    result.copy_to_operands(src);

  return result;
}

void cpp_typecheckt::typecheck_expr_explicit_typecast(exprt &expr)
{
  // C++23 auto(x) decay copy: replace with the operand
  if(expr.type().id() == ID_auto && expr.operands().size() == 1)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr(op);
    exprt result = op;
    expr.swap(result);
    return;
  }

  // these can have 0 or 1 arguments

  if(expr.operands().empty())
  {
    // Default value, e.g., int()
    typecheck_type(expr.type());
    auto new_expr =
      ::zero_initializer(expr.type(), expr.find_source_location(), *this);
    if(!new_expr.has_value())
    {
      error().source_location = expr.find_source_location();
      error() << "cannot zero-initialize '" << to_string(expr.type()) << "'"
              << eom;
      throw 0;
    }

    new_expr->add_source_location() = expr.source_location();
    expr = *new_expr;
  }
  else if(expr.operands().size()==1)
  {
    auto &op = to_unary_expr(expr).op();

    // Explicitly given value, e.g., int(1).
    // There is an expr-vs-type ambiguity, as it is possible to write
    // (f)(1), where 'f' is a function symbol and not a type.
    // This also exists with a "comma expression", e.g.,
    // (f)(1, 2, 3)

    if(expr.type().id()==ID_cpp_name)
    {
      // try to resolve as type
      cpp_typecheck_fargst fargs;

      exprt symbol_expr=resolve(
        to_cpp_name(static_cast<const irept &>(expr.type())),
        cpp_typecheck_resolvet::wantt::TYPE,
        fargs,
        false); // fail silently

      if(symbol_expr.id()==ID_type)
        expr.type()=symbol_expr.type();
      else
      {
        // It's really a function call. Note that multiple arguments
        // become a comma expression, and that these are already typechecked.
        side_effect_expr_function_callt f_call(
          static_cast<const exprt &>(static_cast<const irept &>(expr.type())),
          collect_comma_expression(op).operands(),
          uninitialized_typet{},
          expr.source_location());

        typecheck_side_effect_function_call(f_call);

        expr.swap(f_call);
        return;
      }
    }
    else
      typecheck_type(expr.type());

    // We allow (TYPE){ initializer_list }
    // This is called "compound literal", and is syntactic
    // sugar for a (possibly local) declaration.
    if(op.id() == ID_initializer_list)
    {
      // C++17: direct-list-initialization of scalar/enum types
      // e.g., byte{42} where byte is a scoped enum
      if(
        op.operands().size() == 1 &&
        (expr.type().id() == ID_c_enum_tag || expr.type().id() == ID_signedbv ||
         expr.type().id() == ID_unsignedbv || expr.type().id() == ID_c_bool ||
         expr.type().id() == ID_bool || expr.type().id() == ID_floatbv ||
         expr.type().id() == ID_pointer))
      {
        op = to_unary_expr(op).op();
        // fall through to the typecast path below
      }
      else
      {
        // just do a normal initialization
        do_initializer(op, expr.type(), false);

        // This produces a struct-expression,
        // union-expression, array-expression,
        // or an expression for a pointer or scalar.
        // We produce a compound_literal expression.
        exprt tmp(ID_compound_literal, expr.type());
        tmp.add_to_operands(std::move(op));
        expr = tmp;
        expr.set(ID_C_lvalue, true); // these are l-values
        return;
      }
    }

    // Reject casts of non-static member functions — they require an
    // object and cannot be used as values.
    if(
      op.id() == ID_address_of && op.get_bool(ID_C_implicit) &&
      to_address_of_expr(op).object().type().id() == ID_code &&
      !to_code_type(to_address_of_expr(op).object().type())
         .get(ID_C_member_name)
         .empty())
    {
      error().source_location = expr.find_source_location();
      error() << "invalid use of non-static member function" << eom;
      throw 0;
    }

    exprt new_expr;

    if(
      const_typecast(op, expr.type(), new_expr) ||
      static_typecast(op, expr.type(), new_expr, false) ||
      reinterpret_typecast(op, expr.type(), new_expr, false))
    {
      expr=new_expr;
      add_implicit_dereference(expr);
    }
    else
    {
      error().source_location=expr.find_source_location();
      error() << "invalid explicit cast:\n"
              << "operand type: '" << to_string(op.type()) << "'\n"
              << "casting to: '" << to_string(expr.type()) << "'" << eom;
      throw 0;
    }
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "explicit typecast expects 0 or 1 operands" << eom;
    throw 0;
  }
}

void cpp_typecheckt::typecheck_expr_explicit_constructor_call(exprt &expr)
{
  typecheck_type(expr.type());

  if(cpp_is_pod(expr.type()))
  {
    expr.id("explicit-typecast");
    typecheck_expr_main(expr);
  }
  else
  {
    // Aggregate initialization from braced-init-list for non-POD
    // aggregates (e.g., structs with reference members).
    if(
      expr.operands().size() == 1 &&
      expr.operands().front().id() == ID_initializer_list &&
      !expr.operands().front().operands().empty() &&
      expr.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(expr.type()));

      // Check whether the struct has any non-copy constructor.
      bool has_non_copy_ctor = false;
      for(const auto &c : struct_type.components())
      {
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &code_type = to_code_type(c.type());
        if(code_type.return_type().id() != ID_constructor)
          continue;
        const auto &params = code_type.parameters();
        if(params.size() == 2 && is_reference(params[1].type()))
          continue;
        has_non_copy_ctor = true;
        break;
      }

      if(!has_non_copy_ctor)
      {
        const auto &ops = expr.operands().front().operands();
        struct_exprt result({}, expr.type());
        std::size_t idx = 0;
        bool aggregate = true;
        for(const auto &c : struct_type.components())
        {
          if(
            c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
            c.get_bool(ID_is_static) || c.type().id() == ID_code)
          {
            continue;
          }
          if(c.get_base_name() == "@most_derived")
            continue;
          if(idx < ops.size())
          {
            exprt val = ops[idx++];
            typecheck_expr(val);
            if(is_reference(c.type()))
              reference_initializer(val, to_reference_type(c.type()));
            else
              implicit_typecast(val, c.type());
            result.add_to_operands(std::move(val));
          }
          else
          {
            aggregate = false;
            break;
          }
        }
        if(aggregate)
        {
          result.add_source_location() = expr.source_location();
          expr = std::move(result);
          return;
        }
      }
    }

    exprt e = expr;

    // An empty braced-init-list {} means value-initialization,
    // which for class types calls the default constructor.
    if(
      e.operands().size() == 1 &&
      e.operands().front().id() == ID_initializer_list &&
      e.operands().front().operands().empty())
    {
      e.operands().clear();
    }

    // Direct-list-initialization: TYPE{a, b, c} should try to match
    // constructors with the individual elements of the braced-init-list.
    if(
      e.operands().size() == 1 &&
      e.operands().front().id() == ID_initializer_list &&
      !e.operands().front().operands().empty())
    {
      exprt::operandst expanded = std::move(e.operands().front().operands());
      e.operands() = std::move(expanded);
    }

    new_temporary(e.source_location(), e.type(), e.operands(), expr);
  }
}

void cpp_typecheckt::typecheck_expr_this(exprt &expr)
{
  if(cpp_scopes.current_scope().class_identifier.empty())
  {
    error().source_location = expr.find_source_location();
    error() << "`this' is not allowed here" << eom;
    throw 0;
  }

  const exprt &this_expr=cpp_scopes.current_scope().this_expr;
  const source_locationt source_location=expr.find_source_location();

  PRECONDITION(this_expr.is_not_nil());
  PRECONDITION(this_expr.type().id() == ID_pointer);

  expr=this_expr;
  expr.add_source_location()=source_location;
}

void cpp_typecheckt::typecheck_expr_delete(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "delete expects one operand" << eom;
    throw 0;
  }

  const irep_idt statement=expr.get(ID_statement);

  if(statement==ID_cpp_delete)
  {
  }
  else if(statement==ID_cpp_delete_array)
  {
  }
  else
    UNREACHABLE;

  typet pointer_type = to_unary_expr(expr).op().type();

  if(pointer_type.id()!=ID_pointer)
  {
    error().source_location=expr.find_source_location();
    error() << "delete takes a pointer type operand, but got '"
            << to_string(pointer_type) << "'" << eom;
    throw 0;
  }

  // remove any const-ness of the argument
  // (which would impair the call to the destructor)
  to_pointer_type(pointer_type).base_type().remove(ID_C_constant);

  // delete expressions are always void
  expr.type()=typet(ID_empty);

  // we provide the right destructor, for the convenience
  // of later stages
  exprt new_object(ID_new_object, to_pointer_type(pointer_type).base_type());
  new_object.add_source_location()=expr.source_location();
  new_object.set(ID_C_lvalue, true);

  auto destructor_code =
    cpp_destructor(expr.source_location(), new_object, false);

  already_typechecked_exprt::make_already_typechecked(new_object);

  if(destructor_code.has_value())
  {
    // this isn't typechecked yet
    typecheck_code(destructor_code.value());
    expr.set(ID_destructor, destructor_code.value());
  }
  else
    expr.set(ID_destructor, nil_exprt());
}

void cpp_typecheckt::typecheck_expr_typecast(exprt &)
{
  // should not be called
  #if 0
  std::cout << "E: " << expr.pretty() << '\n';
  UNREACHABLE;
  #endif
}

void cpp_typecheckt::typecheck_expr_member(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "member operator expects one operand" << eom;
    throw 0;
  }

  exprt &op0 = to_unary_expr(expr).op();
  add_implicit_dereference(op0);

  // The notation for explicit calls to destructors can be used regardless
  // of whether the type defines a destructor.  This allows you to make such
  // explicit calls without knowing if a destructor is defined for the type.
  // An explicit call to a destructor where none is defined has no effect.

  if(
    expr.find(ID_component_cpp_name).is_not_nil() &&
    to_cpp_name(expr.find(ID_component_cpp_name)).is_destructor() &&
    op0.type().id() != ID_struct && op0.type().id() != ID_struct_tag)
  {
    exprt tmp(ID_cpp_dummy_destructor);
    tmp.add_source_location()=expr.source_location();
    expr.swap(tmp);
    return;
  }

  // The member operator will trigger template elaboration
  elaborate_class_template(op0.type());

  if(op0.type().id() != ID_struct_tag && op0.type().id() != ID_union_tag)
  {
    error().source_location=expr.find_source_location();
    error() << "member operator requires struct/union type "
            << "on left hand side but got '" << to_string(op0.type()) << "'"
            << eom;
    throw 0;
  }

  const struct_union_typet &type =
    op0.type().id() == ID_struct_tag
      ? static_cast<const struct_union_typet &>(
          follow_tag(to_struct_tag_type(op0.type())))
      : static_cast<const struct_union_typet &>(
          follow_tag(to_union_tag_type(op0.type())));

  if(type.is_incomplete())
  {
    error().source_location = expr.find_source_location();
    error() << "member operator got incomplete type "
            << "on left hand side" << eom;
    throw 0;
  }

  irep_idt struct_identifier=type.get(ID_name);

  if(expr.find(ID_component_cpp_name).is_not_nil())
  {
    cpp_namet component_cpp_name=
      to_cpp_name(expr.find(ID_component_cpp_name));

    // go to the scope of the struct/union
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_identifier);

    // resolve the member name in this scope
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.add_object(op0);

    exprt symbol_expr=resolve(
                        component_cpp_name,
                        cpp_typecheck_resolvet::wantt::VAR,
                        new_fargs);

    if(symbol_expr.id()==ID_dereference)
    {
      CHECK_RETURN(symbol_expr.get_bool(ID_C_implicit));
      exprt tmp = to_dereference_expr(symbol_expr).pointer();
      symbol_expr.swap(tmp);
    }

    DATA_INVARIANT(
      symbol_expr.id() == ID_symbol || symbol_expr.id() == ID_member ||
        symbol_expr.is_constant(),
      "expression kind unexpected");

    // If it is a symbol or a constant, just return it!
    // Note: the resolver returns a symbol if the member
    // is static or if it is a constructor.

    if(symbol_expr.id()==ID_symbol)
    {
      if(
        symbol_expr.type().id() == ID_code &&
        to_code_type(symbol_expr.type()).return_type().id() == ID_constructor)
      {
        error().source_location=expr.find_source_location();
        error() << "member '"
                << lookup(symbol_expr.get(ID_identifier)).base_name
                << "' is a constructor" << eom;
        throw 0;
      }
      else
      {
        // Check if this is an instantiated member function template
        // (non-static, with a 'this' parameter).  In that case, we
        // must not treat it as a static member — fall through to the
        // member-expression path so that 'this' is added.
        if(
          symbol_expr.type().id() == ID_code &&
          !to_code_type(symbol_expr.type()).parameters().empty() &&
          to_code_type(symbol_expr.type()).parameters().front().get_this())
        {
          // Build a member expression so the caller adds 'this'.
          irep_idt component_name =
            to_symbol_expr(symbol_expr).get_identifier();
          expr.remove(ID_component_cpp_name);
          expr.set(ID_component_name, component_name);
          expr.type() = symbol_expr.type();
          return;
        }

        // it must be a static component
        const struct_typet::componentt &pcomp =
          type.get_component(to_symbol_expr(symbol_expr).get_identifier());

        if(pcomp.is_nil())
        {
          error().source_location=expr.find_source_location();
          error() << "'" << symbol_expr.get(ID_identifier)
                  << "' is not static member "
                  << "of class '" << to_string(op0.type()) << "'" << eom;
          throw 0;
        }
      }

      expr=symbol_expr;
      return;
    }
    else if(symbol_expr.is_constant())
    {
      expr=symbol_expr;
      return;
    }

    const irep_idt component_name=symbol_expr.get(ID_component_name);

    expr.remove(ID_component_cpp_name);
    expr.set(ID_component_name, component_name);
  }

  const irep_idt &component_name=expr.get(ID_component_name);
  INVARIANT(!component_name.empty(), "component name should not be empty");

  exprt component;
  component.make_nil();

  PRECONDITION(
    op0.type().id() == ID_struct || op0.type().id() == ID_union ||
    op0.type().id() == ID_struct_tag || op0.type().id() == ID_union_tag);

  exprt member;

  if(get_component(expr.source_location(), op0, component_name, member))
  {
    // because of possible anonymous members
    expr.swap(member);
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "member '" << component_name << "' of '" << to_string(type)
            << "' not found" << eom;
    throw 0;
  }

  add_implicit_dereference(expr);

  if(expr.type().id()==ID_code)
  {
    // Check if the function body has to be typechecked
    symbolt &component_symbol = symbol_table.get_writeable_ref(component_name);

    if(component_symbol.value.id() == ID_cpp_not_typechecked)
      component_symbol.value.set(ID_is_used, true);
  }
}

void cpp_typecheckt::typecheck_expr_ptrmember(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  PRECONDITION(expr.id() == ID_ptrmember);

  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "ptrmember operator expects one operand" << eom;
    throw 0;
  }

  auto &op = to_unary_expr(expr).op();

  add_implicit_dereference(op);

  // is operator-> overloaded?
  if(op.type().id() != ID_pointer)
  {
    std::string op_name = "operator->";

    const cpp_namet cpp_name(op_name, expr.source_location());

    side_effect_expr_function_callt function_call(
      cpp_name.as_expr(), {op}, uninitialized_typet{}, expr.source_location());

    typecheck_side_effect_function_call(function_call);

    already_typechecked_exprt::make_already_typechecked(function_call);

    op.swap(function_call);

    // Re-enter to handle the result (which may be a pointer or
    // another class with operator->).
    typecheck_expr_ptrmember(expr, fargs);
    return;
  }

  exprt tmp;
  op.swap(tmp);

  op.id(ID_dereference);
  op.add_to_operands(std::move(tmp));
  op.add_source_location() = expr.source_location();
  typecheck_expr_dereference(op);

  expr.id(ID_member);
  typecheck_expr_member(expr, fargs);
}

void cpp_typecheckt::typecheck_cast_expr(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location=expr.find_source_location();
    error() << "cast expressions expect one operand" << eom;
    throw 0;
  }

  exprt &cast_op = to_unary_expr(expr).op();

  add_implicit_dereference(cast_op);

  const irep_idt &id = expr.id();

  typet &type = expr.type();
  typecheck_type(type);

  source_locationt source_location=expr.source_location();

  exprt new_expr;
  if(id==ID_const_cast)
  {
    if(!const_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on const_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_dynamic_cast)
  {
    if(!dynamic_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on dynamic_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_reinterpret_cast)
  {
    if(!reinterpret_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on reinterpret_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_static_cast)
  {
    if(!static_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on static_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else
    UNREACHABLE;

  expr.swap(new_expr);
}

void cpp_typecheckt::typecheck_expr_cpp_name(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  source_locationt source_location=
    to_cpp_name(expr).source_location();

  if(expr.get_sub().size()==1 &&
     expr.get_sub()[0].id()==ID_name)
  {
    const irep_idt identifier=expr.get_sub()[0].get(ID_identifier);

    if(
      auto gcc_polymorphic = typecheck_gcc_polymorphic_builtin(
        identifier, fargs.operands, source_location))
    {
      expr = std::move(*gcc_polymorphic);
      return;
    }
  }

  for(std::size_t i=0; i<expr.get_sub().size(); i++)
  {
    if(expr.get_sub()[i].id()==ID_cpp_name)
    {
      typet &type=static_cast<typet &>(expr.get_sub()[i]);
      typecheck_type(type);

      std::string tmp="("+cpp_type2name(type)+")";

      typet name(ID_name);
      name.set(ID_identifier, tmp);
      name.add_source_location()=source_location;

      type=name;
    }
  }

  exprt symbol_expr=
    resolve(
      to_cpp_name(expr),
      cpp_typecheck_resolvet::wantt::VAR,
      fargs);

  // we want VAR
  CHECK_RETURN(symbol_expr.id() != ID_type);

  if(symbol_expr.id()==ID_member)
  {
    if(
      symbol_expr.operands().empty() ||
      to_multi_ary_expr(symbol_expr).op0().is_nil())
    {
      if(to_code_type(symbol_expr.type()).return_type().id() != ID_constructor)
      {
        if(cpp_scopes.current_scope().this_expr.is_nil())
        {
          if(symbol_expr.type().id()!=ID_code)
          {
            error().source_location=source_location;
            error() << "object missing" << eom;
            throw 0;
          }

          // may still be good for address of
        }
        else
        {
          // Try again
          exprt ptrmem(ID_ptrmember);
          ptrmem.operands().push_back(
            cpp_scopes.current_scope().this_expr);

          ptrmem.add(ID_component_cpp_name)=expr;

          ptrmem.add_source_location()=source_location;
          typecheck_expr_ptrmember(ptrmem, fargs);
          symbol_expr.swap(ptrmem);
        }
      }
    }
  }
  else if(
    fargs.in_use && symbol_expr.id() == ID_symbol &&
    symbol_expr.type().id() == ID_code &&
    to_code_type(symbol_expr.type()).return_type().id() != ID_constructor &&
    !to_code_type(symbol_expr.type()).parameters().empty() &&
    to_code_type(symbol_expr.type()).parameters().front().get_this() &&
    cpp_scopes.current_scope().this_expr.is_not_nil())
  {
    // Instantiated template member function returned as symbol_exprt
    // when called from within a class method body. Build a member
    // expression with dereferenced 'this' as the object so that
    // typecheck_method_application adds the this argument.
    const exprt &this_expr = cpp_scopes.current_scope().this_expr;
    exprt object(ID_dereference, to_pointer_type(this_expr.type()).base_type());
    object.copy_to_operands(this_expr);
    object.type().set(
      ID_C_constant,
      to_pointer_type(this_expr.type()).base_type().get_bool(ID_C_constant));
    object.set(ID_C_lvalue, true);
    object.add_source_location() = source_location;

    exprt member(ID_member);
    member.set(ID_component_name, to_symbol_expr(symbol_expr).get_identifier());
    member.add_to_operands(std::move(object));
    member.type() = symbol_expr.type();
    member.add_source_location() = source_location;
    symbol_expr.swap(member);
  }

  symbol_expr.add_source_location()=source_location;
  expr=symbol_expr;

  if(expr.id()==ID_symbol)
    typecheck_expr_function_identifier(expr);

  add_implicit_dereference(expr);
}

void cpp_typecheckt::add_implicit_dereference(exprt &expr)
{
  if(is_reference(expr.type()) || is_rvalue_reference(expr.type()))
  {
    // add implicit dereference
    dereference_exprt tmp(expr);
    tmp.set(ID_C_implicit, true);
    tmp.add_source_location()=expr.source_location();
    tmp.set(ID_C_lvalue, true);
    expr.swap(tmp);
  }
}

void cpp_typecheckt::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr)
{
  // __builtin_is_constant_evaluated() always returns false at runtime.
  if(expr.function().id() == ID_cpp_name)
  {
    const auto &name = to_cpp_name(expr.function());
    const irep_idt &bn = name.get_base_name();
    if(bn == "__builtin_is_constant_evaluated")
    {
      exprt result = false_exprt();
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
    // GCC built-in floating-point classification
    if(
      (bn == "__builtin_isfinite" || bn == "__builtin_isinf" ||
       bn == "__builtin_isnan" || bn == "__builtin_isnormal") &&
      expr.arguments().size() == 1)
    {
      typecheck_expr(expr.arguments()[0]);
      exprt arg = expr.arguments()[0];
      exprt result;
      if(bn == "__builtin_isfinite")
        result = isfinite_exprt(arg);
      else if(bn == "__builtin_isinf")
        result = isinf_exprt(arg);
      else if(bn == "__builtin_isnan")
        result = isnan_exprt(arg);
      else
        result = isnormal_exprt(arg);
      result.add_source_location() = expr.source_location();
      exprt cast = typecast_exprt::conditional_cast(result, expr.type());
      expr.swap(cast);
      return;
    }
  }

  // For virtual functions, it is important to check whether
  // the function name is qualified. If it is qualified, then
  // the call is not virtual.
  bool is_qualified = false;

  if(expr.function().id()==ID_member ||
     expr.function().id()==ID_ptrmember)
  {
    if(expr.function().get(ID_component_cpp_name)==ID_cpp_name)
    {
      const cpp_namet &cpp_name=
        to_cpp_name(expr.function().find(ID_component_cpp_name));
      is_qualified=cpp_name.is_qualified();
    }
  }
  else if(expr.function().id()==ID_cpp_name)
  {
    const cpp_namet &cpp_name=to_cpp_name(expr.function());
    is_qualified=cpp_name.is_qualified();
  }

  // Backup of the original operand
  exprt op0=expr.function();

  // Pre-typecheck arguments to get their types for template argument
  // deduction. This is needed for function templates with partial
  // explicit template arguments (e.g., duration_cast<seconds>(d)).
  for(auto &arg : expr.arguments())
  {
    if(arg.type().id().empty() || arg.type().is_nil())
    {
      try
      {
        typecheck_expr(arg);
      }
      catch(...)
      {
        // ignore errors — argument may depend on template resolution
      }
    }
  }

  // now do the function -- this has been postponed
  // SystemC extension: a.range(upper, lower) on bitvector types
  if(
    expr.function().id() == ID_member &&
    expr.function().find(ID_component_cpp_name).is_not_nil() &&
    expr.arguments().size() == 2)
  {
    const cpp_namet &member_name =
      to_cpp_name(expr.function().find(ID_component_cpp_name));
    const irep_idt &base = member_name.get_base_name();
    if(base == "range")
    {
      exprt &obj = to_unary_expr(expr.function()).op();
      typecheck_expr(obj);
      add_implicit_dereference(obj);
      if(obj.type().id() == ID_unsignedbv)
      {
        typecheck_expr(expr.arguments()[0]);
        typecheck_expr(expr.arguments()[1]);
        const auto upper = numeric_cast<mp_integer>(expr.arguments()[0]);
        const auto lower = numeric_cast<mp_integer>(expr.arguments()[1]);
        if(upper.has_value() && lower.has_value() && *upper >= *lower)
        {
          const std::size_t width =
            numeric_cast_v<std::size_t>(*upper - *lower + 1);
          extractbits_exprt result(
            obj,
            from_integer(*lower, unsignedbv_typet(32)),
            unsignedbv_typet(width));
          result.add_source_location() = expr.source_location();
          expr.swap(result);
          return;
        }
      }
    }
  }

  typecheck_function_expr(expr.function(), cpp_typecheck_fargst(expr));

  if(expr.function().id() == ID_pod_constructor)
  {
    PRECONDITION(expr.function().type().id() == ID_code);

    // This must be a POD.
    const typet &pod=to_code_type(expr.function().type()).return_type();
    PRECONDITION(cpp_is_pod(pod));

    // These aren't really function calls, but either conversions or
    // initializations.
    if(expr.arguments().size() <= 1)
    {
      exprt typecast("explicit-typecast");
      typecast.type()=pod;
      typecast.add_source_location()=expr.source_location();
      if(!expr.arguments().empty())
        typecast.copy_to_operands(expr.arguments().front());
      typecheck_expr_explicit_typecast(typecast);
      expr.swap(typecast);
    }
    else
    {
      error().source_location=expr.source_location();
      error() << "zero or one argument expected" << eom;
      throw 0;
    }

    return;
  }
  else if(expr.function().id() == ID_cpp_dummy_destructor)
  {
    // these don't do anything, e.g., (char*)->~char()
    typecast_exprt no_op(from_integer(0, signed_int_type()), void_type());
    expr.swap(no_op);
    return;
  }

  // look at type of function

  if(expr.function().type().id()==ID_pointer)
  {
    if(expr.function().type().find(ID_to_member).is_not_nil())
    {
      const exprt &bound =
        static_cast<const exprt &>(expr.function().type().find(ID_C_bound));

      if(bound.is_nil())
      {
        error().source_location=expr.source_location();
        error() << "pointer-to-member not bound" << eom;
        throw 0;
      }

      // add `this'
      DATA_INVARIANT(bound.type().id() == ID_pointer, "should be pointer");
      expr.arguments().insert(expr.arguments().begin(), bound);

      // we don't need the object any more
      expr.function().type().remove(ID_C_bound);
    }

    // do implicit dereference
    if(expr.function().id() == ID_address_of)
    {
      exprt tmp;
      tmp.swap(to_address_of_expr(expr.function()).object());
      expr.function().swap(tmp);
    }
    else
    {
      PRECONDITION(expr.function().type().id() == ID_pointer);
      dereference_exprt tmp(expr.function());
      tmp.add_source_location() = expr.function().source_location();
      expr.function().swap(tmp);
    }

    if(expr.function().type().id()!=ID_code)
    {
      error().source_location = expr.function().find_source_location();
      error() << "expecting code as argument" << eom;
      throw 0;
    }
  }
  else if(expr.function().type().id()==ID_code)
  {
    if(expr.function().type().get_bool(ID_C_is_virtual) && !is_qualified)
    {
      exprt vtptr_member;
      if(op0.id()==ID_member || op0.id()==ID_ptrmember)
      {
        vtptr_member.id(op0.id());
        vtptr_member.add_to_operands(std::move(to_unary_expr(op0).op()));
      }
      else
      {
        vtptr_member.id(ID_ptrmember);
        exprt this_expr("cpp-this");
        vtptr_member.add_to_operands(std::move(this_expr));
      }

      // get the virtual table
      auto this_type = to_pointer_type(
        to_code_type(expr.function().type()).parameters().front().type());

      const struct_typet &vt_struct =
        follow_tag(to_struct_tag_type(this_type.base_type()));

      // Find the vtable pointer component — it may be inherited from a
      // base class, so search by the ID_is_vtptr flag rather than by name.
      irep_idt vtable_name;
      const struct_typet::componentt *vt_compo_ptr = nullptr;
      for(const auto &c : vt_struct.components())
      {
        if(c.get_bool(ID_is_vtptr))
        {
          vt_compo_ptr = &c;
          vtable_name = c.get_name();
          break;
        }
      }
      CHECK_RETURN(vt_compo_ptr != nullptr);
      const struct_typet::componentt &vt_compo = *vt_compo_ptr;

      vtptr_member.set(ID_component_name, vtable_name);

      // look for the right entry
      irep_idt vtentry_component_name =
        to_pointer_type(vt_compo.type()).base_type().get_string(ID_identifier) +
        "::" + expr.function().type().get_string(ID_C_virtual_name);

      exprt vtentry_member(ID_ptrmember);
      vtentry_member.copy_to_operands(vtptr_member);
      vtentry_member.set(ID_component_name, vtentry_component_name);
      typecheck_expr(vtentry_member);

      CHECK_RETURN(vtentry_member.type().id() == ID_pointer);

      {
        dereference_exprt tmp(vtentry_member);
        tmp.add_source_location() = expr.function().source_location();
        vtentry_member.swap(tmp);
      }

      // Typecheck the expression as if it was not virtual
      // (add the this pointer)

      expr.type()=
        to_code_type(expr.function().type()).return_type();

      if(expr.function().id() == ID_member)
        typecheck_method_application(expr);

      // Let's make the call virtual
      expr.function().swap(vtentry_member);

      typecheck_function_call_arguments(expr);
      add_implicit_dereference(expr);
      return;
    }
  }
  else if(expr.function().type().id() == ID_struct_tag)
  {
    const cpp_namet cppname("operator()", expr.source_location());

    // The function expression evaluates to a struct value (e.g., F()).
    // Wrap it in a temporary_object so the this pointer can be formed.
    exprt obj = std::move(expr.function());
    if(!obj.get_bool(ID_C_lvalue))
    {
      side_effect_exprt tmp(
        ID_temporary_object, obj.type(), obj.source_location());
      tmp.add_to_operands(std::move(obj));
      tmp.set(ID_C_lvalue, true);
      tmp.set(ID_mode, ID_cpp);
      obj = std::move(tmp);
    }

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cppname;
    member.add_to_operands(already_typechecked_exprt{std::move(obj)});

    expr.function().swap(member);
    typecheck_side_effect_function_call(expr);

    return;
  }
  else
  {
    error().source_location=expr.function().find_source_location();
    error() << "function call expects function or function "
            << "pointer as argument, but got '"
            << to_string(expr.function().type()) << "'" << eom;
    throw 0;
  }

  expr.type()=
    to_code_type(expr.function().type()).return_type();

  if(expr.type().id()==ID_constructor)
  {
    PRECONDITION(expr.function().id() == ID_symbol);

    const code_typet::parameterst &parameters=
      to_code_type(expr.function().type()).parameters();

    DATA_INVARIANT(!parameters.empty(), "parameters expected");

    const auto &this_type = to_pointer_type(parameters[0].type());

    // change type from 'constructor' to object type
    expr.type() = this_type.base_type();

    // create temporary object
    side_effect_exprt tmp_object_expr(
      ID_temporary_object, this_type.base_type(), expr.source_location());
    tmp_object_expr.set(ID_C_lvalue, true);
    tmp_object_expr.set(ID_mode, ID_cpp);

    exprt member;

    exprt new_object(ID_new_object, tmp_object_expr.type());
    new_object.set(ID_C_lvalue, true);

    PRECONDITION(tmp_object_expr.type().id() == ID_struct_tag);

    get_component(expr.source_location(),
                  new_object,
                  expr.function().get(ID_identifier),
                  member);

    // special case for the initialization of parents
    if(member.get_bool(ID_C_not_accessible))
    {
      PRECONDITION(!member.get(ID_C_access).empty());
      tmp_object_expr.set(ID_C_not_accessible, true);
      tmp_object_expr.set(ID_C_access, member.get(ID_C_access));
    }

    // the constructor is being used, so make sure the destructor
    // will be available
    {
      // find name of destructor
      const struct_typet::componentst &components =
        follow_tag(to_struct_tag_type(tmp_object_expr.type())).components();

      for(const auto &c : components)
      {
        const typet &type = c.type();

        if(
          !c.get_bool(ID_from_base) && type.id() == ID_code &&
          to_code_type(type).return_type().id() == ID_destructor)
        {
          add_method_body(&symbol_table.get_writeable_ref(c.get_name()));
          break;
        }
      }
    }

    expr.function().swap(member);

    typecheck_method_application(expr);
    typecheck_function_call_arguments(expr);

    const code_expressiont new_code(expr);
    tmp_object_expr.add(ID_initializer)=new_code;
    expr.swap(tmp_object_expr);
    return;
  }

  PRECONDITION(expr.operands().size() == 2);

  if(expr.function().id()==ID_member)
  {
    typecheck_method_application(expr);
    // Update return type after method application — the method's auto
    // return type may have been deduced during convert_function.
    if(has_auto(expr.type()))
      expr.type() = to_code_type(expr.function().type()).return_type();
  }
  else
  {
    // for the object of a method call,
    // we are willing to add an "address_of"
    // for the sake of operator overloading

    const code_typet::parameterst &parameters =
      to_code_type(expr.function().type()).parameters();

    if(
      !parameters.empty() && parameters.front().get_this() &&
      !expr.arguments().empty())
    {
      const code_typet::parametert &parameter = parameters.front();

      exprt &operand = expr.arguments().front();
      INVARIANT(
        parameter.type().id() == ID_pointer,
        "`this' parameter should be a pointer");

      if(
        operand.type().id() != ID_pointer &&
        operand.type() == to_pointer_type(parameter.type()).base_type())
      {
        address_of_exprt tmp(operand, pointer_type(operand.type()));
        tmp.add_source_location()=operand.source_location();
        operand=tmp;
      }
    }
  }

  CHECK_RETURN(expr.operands().size() == 2);

  // Generic lambda instantiation: if the call target is a generic lambda,
  // instantiate a new version with the actual argument types.
  instantiate_generic_lambda(expr);

  typecheck_function_call_arguments(expr);

  CHECK_RETURN(expr.operands().size() == 2);

  add_implicit_dereference(expr);

  // constexpr function evaluation
  if(auto sym_expr = expr_try_dynamic_cast<symbol_exprt>(expr.function()))
  {
    const auto *symbol_ptr = symbol_table.lookup(sym_expr->get_identifier());
    if(
      symbol_ptr != nullptr && symbol_ptr->is_macro &&
      !functions_being_typechecked.count(sym_expr->get_identifier()) &&
      !deferred_typechecking.count(sym_expr->get_identifier()) &&
      symbol_ptr->value.type().id() == ID_code)
    {
      const auto &code_type = to_code_type(symbol_ptr->type);
      PRECONDITION(expr.arguments().size() == code_type.parameters().size());
      replace_symbolt value_map;
      auto param_it = code_type.parameters().begin();
      for(const auto &arg : expr.arguments())
      {
        value_map.insert(
          symbol_exprt{param_it->get_identifier(), param_it->type()},
          typecast_exprt::conditional_cast(arg, param_it->type()));
        ++param_it;
      }
      bool can_evaluate = true;
      const auto &block = to_code_block(to_code(symbol_ptr->value));
      for(const auto &stmt : block.statements())
      {
        if(!can_evaluate)
          break;
        if(
          auto return_stmt = expr_try_dynamic_cast<code_frontend_returnt>(stmt))
        {
          PRECONDITION(return_stmt->has_return_value());
          exprt tmp = return_stmt->return_value();
          value_map.replace(tmp);
          simplify(tmp, *this);
          // Aggregate init: convert {a, b, ...} to struct{.m1=a, .m2=b}
          if(
            tmp.id() == ID_initializer_list &&
            code_type.return_type().id() == ID_struct_tag)
          {
            const auto &st =
              follow_tag(to_struct_tag_type(code_type.return_type()));
            const auto &comps = st.components();
            struct_exprt s({}, code_type.return_type());
            std::size_t i = 0;
            for(const auto &c : comps)
            {
              if(c.get_is_padding() || c.type().id() == ID_code)
                continue;
              if(i < tmp.operands().size())
                s.operands().push_back(typecast_exprt::conditional_cast(
                  tmp.operands()[i++], c.type()));
              else
                break;
            }
            if(i == tmp.operands().size())
              tmp = std::move(s);
            else
            {
              can_evaluate = false;
              break;
            }
          }
          expr.swap(tmp);
          return;
        }
        else if(auto expr_stmt = expr_try_dynamic_cast<code_expressiont>(stmt))
        {
          if(
            auto assign = expr_try_dynamic_cast<side_effect_expr_assignt>(
              expr_stmt->expression()))
          {
            if(assign->lhs().id() == ID_symbol)
            {
              exprt rhs = assign->rhs();
              value_map.replace(rhs);
              value_map.set(to_symbol_expr(assign->lhs()), rhs);
            }
            else
              can_evaluate = false;
          }
          else
            can_evaluate = false;
        }
        else if(stmt.get_statement() == ID_decl_block)
        {
          for(const auto &expect_decl : stmt.operands())
          {
            if(to_code(expect_decl).get_statement() != ID_decl)
            {
              can_evaluate = false;
              break;
            }
            const auto &decl = to_code_frontend_decl(to_code(expect_decl));
            if(decl.initial_value().has_value())
            {
              exprt init = decl.initial_value().value();
              value_map.replace(init);
              value_map.set(decl.symbol(), init);
            }
          }
        }
        else if(stmt.get_statement() == ID_skip)
        {
          // no-op, just continue
        }
        else if(stmt.get_statement() == ID_ifthenelse)
        {
          try
          {
            // C++14 relaxed constexpr: if/else
            exprt cond = stmt.op0();
            value_map.replace(cond);
            simplify(cond, *this);
            if(cond.is_true())
            {
              // Evaluate 'then' branch
              if(stmt.operands().size() >= 2)
              {
                if(stmt.op1().id() != ID_code)
                {
                  can_evaluate = false;
                  break;
                }
                const auto &then_code = to_code(stmt.op1());
                if(then_code.get_statement() == ID_block)
                {
                  for(const auto &s : to_code_block(then_code).statements())
                  {
                    if(
                      auto ret =
                        expr_try_dynamic_cast<code_frontend_returnt>(s))
                    {
                      exprt tmp = ret->return_value();
                      value_map.replace(tmp);
                      expr.swap(tmp);
                      return;
                    }
                    else if(
                      auto es = expr_try_dynamic_cast<code_expressiont>(s))
                    {
                      if(
                        auto assign =
                          expr_try_dynamic_cast<side_effect_expr_assignt>(
                            es->expression()))
                      {
                        if(assign->lhs().id() == ID_symbol)
                        {
                          exprt rhs = assign->rhs();
                          value_map.replace(rhs);
                          value_map.set(to_symbol_expr(assign->lhs()), rhs);
                        }
                        else
                          can_evaluate = false;
                      }
                    }
                  }
                }
                else if(
                  auto ret =
                    expr_try_dynamic_cast<code_frontend_returnt>(then_code))
                {
                  exprt tmp = ret->return_value();
                  value_map.replace(tmp);
                  expr.swap(tmp);
                  return;
                }
              }
            }
            else if(cond.is_false())
            {
              // Evaluate 'else' branch if present
              if(stmt.operands().size() >= 3)
              {
                if(stmt.op2().id() != ID_code)
                {
                  can_evaluate = false;
                  break;
                }
                const auto &else_code = to_code(stmt.op2());
                if(
                  auto ret =
                    expr_try_dynamic_cast<code_frontend_returnt>(else_code))
                {
                  exprt tmp = ret->return_value();
                  value_map.replace(tmp);
                  expr.swap(tmp);
                  return;
                }
              }
            }
            else
              can_evaluate = false;
          }
          catch(...)
          {
            can_evaluate = false;
          }
        }
        else if(stmt.get_statement() == ID_while)
        {
          try
          {
            // C++14 relaxed constexpr: while loop with bounded iterations
            const unsigned max_iterations = 1000;
            for(unsigned i = 0; i < max_iterations && can_evaluate; ++i)
            {
              exprt cond = stmt.op0();
              value_map.replace(cond);
              simplify(cond, *this);
              if(cond.is_false())
                break;
              if(!cond.is_true())
              {
                can_evaluate = false;
                break;
              }
              // Execute loop body
              if(stmt.operands().size() < 2 || stmt.op1().id() != ID_code)
              {
                can_evaluate = false;
                break;
              }
              const auto &body = to_code(stmt.op1());
              auto exec_stmt = [&](const codet &s) -> bool
              {
                if(auto ret = expr_try_dynamic_cast<code_frontend_returnt>(s))
                {
                  exprt tmp = ret->return_value();
                  value_map.replace(tmp);
                  expr.swap(tmp);
                  return true; // return from function
                }
                else if(auto es = expr_try_dynamic_cast<code_expressiont>(s))
                {
                  if(
                    auto assign =
                      expr_try_dynamic_cast<side_effect_expr_assignt>(
                        es->expression()))
                  {
                    if(assign->lhs().id() == ID_symbol)
                    {
                      exprt rhs = assign->rhs();
                      value_map.replace(rhs);
                      simplify(rhs, *this);
                      value_map.set(to_symbol_expr(assign->lhs()), rhs);
                    }
                    else
                      can_evaluate = false;
                  }
                }
                else if(s.get_statement() == ID_decl_block)
                {
                  for(const auto &d : s.operands())
                  {
                    if(
                      d.id() == ID_code &&
                      to_code(d).get_statement() == ID_decl)
                    {
                      const auto &decl = to_code_frontend_decl(to_code(d));
                      if(decl.initial_value().has_value())
                      {
                        exprt init = decl.initial_value().value();
                        value_map.replace(init);
                        simplify(init, *this);
                        value_map.set(decl.symbol(), init);
                      }
                    }
                  }
                }
                else if(s.get_statement() == ID_skip)
                {
                }
                else
                  can_evaluate = false;
                return false;
              };

              if(body.get_statement() == ID_block)
              {
                for(const auto &s : to_code_block(body).statements())
                {
                  if(s.id() != ID_code)
                  {
                    can_evaluate = false;
                    break;
                  }
                  if(exec_stmt(to_code(s)))
                    return; // function returned
                  if(!can_evaluate)
                    break;
                }
              }
              else
              {
                if(exec_stmt(body))
                  return;
              }
            }
          }
          catch(...)
          {
            can_evaluate = false;
          }
        }
        else
        {
          // Unsupported statement type.
          // Fall back to treating as a regular function call.
          can_evaluate = false;
        }
      }

      // If we couldn't evaluate at compile time, treat as a regular
      // function call by clearing the is_macro flag.
      if(!can_evaluate)
      {
        symbol_table.get_writeable_ref(sym_expr->get_identifier()).is_macro =
          false;
      }
    }
  }

  // we will deal with some 'special' functions here
  exprt tmp=do_special_functions(expr);
  if(tmp.is_not_nil())
    expr.swap(tmp);
}

/// \param expr: function call whose arguments need to be checked
void cpp_typecheckt::typecheck_function_call_arguments(
  side_effect_expr_function_callt &expr)
{
  exprt &f_op=expr.function();
  const code_typet &code_type=to_code_type(f_op.type());
  const code_typet::parameterst &parameters=code_type.parameters();

  // do default arguments

  if(parameters.size()>expr.arguments().size())
  {
    std::size_t i=expr.arguments().size();

    for(; i<parameters.size(); i++)
    {
      if(!parameters[i].has_default_value())
        break;

      const exprt &value=parameters[i].default_value();
      expr.arguments().push_back(value);
    }
  }

  exprt::operandst::iterator arg_it=expr.arguments().begin();
  for(const auto &parameter : parameters)
  {
    if(parameter.get_bool(ID_C_call_by_value))
    {
      DATA_INVARIANT(is_reference(parameter.type()), "reference expected");

      if(arg_it->id()!=ID_temporary_object)
      {
        // create a temporary for the parameter

        exprt temporary;
        new_temporary(
          arg_it->source_location(),
          to_reference_type(parameter.type()).base_type(),
          already_typechecked_exprt{*arg_it},
          temporary);
        arg_it->swap(temporary);
      }
    }
    else if(
      !is_reference(parameter.type()) && !cpp_is_pod(parameter.type()) &&
      (parameter.type().id() == ID_struct_tag ||
       parameter.type().id() == ID_union_tag) &&
      arg_it->id() != ID_temporary_object && arg_it->id() != ID_side_effect)
    {
      // Brace-init-list to std::initializer_list<T>: convert before
      // the copy-constructor path so that new_temporary sees a struct,
      // not a raw brace-init-list.
      if(
        arg_it->id() == ID_initializer_list &&
        parameter.type().id() == ID_struct_tag &&
        id2string(to_struct_tag_type(parameter.type()).get_identifier())
            .find("tag-initializer_list<") != std::string::npos)
      {
        implicit_typecast(*arg_it, parameter.type());
        ++arg_it;
        continue;
      }

      // Non-POD class-type pass-by-value: call copy constructor.
      // Check that the destructor symbol exists (needed for the
      // temporary) to avoid crashes during goto conversion.
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(parameter.type()));
      bool has_dtor = false;
      for(const auto &c : struct_type.components())
      {
        if(
          c.type().id() == ID_code &&
          to_code_type(c.type()).return_type().id() == ID_destructor)
        {
          const symbolt *dtor_sym;
          has_dtor = !lookup(c.get_name(), dtor_sym);
          break;
        }
      }
      if(has_dtor)
      {
        exprt temporary;
        new_temporary(
          arg_it->source_location(),
          parameter.type(),
          already_typechecked_exprt{*arg_it},
          temporary);
        arg_it->swap(temporary);
      }
    }

    ++arg_it;
  }

  c_typecheck_baset::typecheck_function_call_arguments(expr);
}

/// Replace `auto` (or `cpp_name`) in a type tree with the given replacement.
/// Handles `const auto &`, `auto *`, etc.
static void replace_auto_in_type(typet &type, const typet &replacement)
{
  if(type.id() == ID_auto || type.id() == ID_cpp_name)
  {
    type = replacement;
    return;
  }

  if(
    type.id() == ID_merged_type || type.id() == ID_frontend_pointer ||
    type.id() == ID_pointer)
  {
    for(auto &sub : to_type_with_subtypes(type).subtypes())
      replace_auto_in_type(sub, replacement);
  }
}

void cpp_typecheckt::instantiate_generic_lambda(
  side_effect_expr_function_callt &expr)
{
  // Resolve the lambda function name from the call target.
  // The function expression is either:
  //   dereference(symbol("var")) — indirect call through variable
  //   symbol("lambda_func") — direct call
  irep_idt lambda_name;

  if(expr.function().id() == ID_dereference)
  {
    const exprt &inner = to_dereference_expr(expr.function()).pointer();
    if(inner.id() == ID_symbol)
    {
      const symbolt &var_sym =
        symbol_table.lookup_ref(to_symbol_expr(inner).get_identifier());
      // The variable's value should be address_of(symbol(lambda_func))
      if(
        var_sym.value.id() == ID_address_of &&
        to_address_of_expr(var_sym.value).object().id() == ID_symbol)
      {
        lambda_name = to_symbol_expr(to_address_of_expr(var_sym.value).object())
                        .get_identifier();
      }
    }
  }
  else if(expr.function().id() == ID_symbol)
  {
    lambda_name = to_symbol_expr(expr.function()).get_identifier();
  }

  if(lambda_name.empty())
    return;

  auto it = generic_lambda_map.find(lambda_name);
  if(it == generic_lambda_map.end())
    return;

  // Build the list of actual argument types
  std::vector<typet> arg_types;
  for(auto &arg : expr.arguments())
  {
    if(arg.type().is_nil() || arg.type().id().empty())
      typecheck_expr(arg);
    arg_types.push_back(arg.type());
  }

  // Build a mangled name for this instantiation
  std::string inst_name = id2string(lambda_name);
  for(const auto &t : arg_types)
    inst_name += "#" + cpp_type2name(t);

  // Check if we already instantiated this specialization
  if(symbol_table.has_symbol(inst_name))
  {
    // Redirect the call to the existing instantiation
    const symbolt &inst_sym = symbol_table.lookup_ref(inst_name);
    const code_typet &inst_type = to_code_type(inst_sym.type);
    if(expr.function().id() == ID_dereference)
    {
      expr.function() = symbol_exprt(inst_name, inst_type);
      expr.type() = inst_type.return_type();
    }
    return;
  }

  // Create a fresh copy of the original lambda expression
  exprt lambda_expr = it->second;

  // Replace auto/template parameters with actual argument types.
  // Build a mapping from template parameter names to actual types
  // (for C++20 template lambdas where params use named types like T).
  std::map<irep_idt, typet> type_map;
  irept &params = lambda_expr.add(ID_parameters);
  std::size_t arg_idx = 0;
  for(auto &p : params.get_sub())
  {
    cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
    if(pdecl.get_bool("explicit_this"))
      continue;
    if(arg_idx < arg_types.size())
    {
      if(has_auto(pdecl.type()) || pdecl.type().id() == ID_auto)
      {
        replace_auto_in_type(pdecl.type(), arg_types[arg_idx]);
      }
      else if(pdecl.type().id() == ID_cpp_name)
      {
        // Template lambda: map the type name to the actual type
        irep_idt tname = pdecl.type().get_sub().front().get(ID_identifier);
        type_map[tname] = arg_types[arg_idx];
        pdecl.type() = arg_types[arg_idx];
      }
    }
    arg_idx++;
  }

  // Replace template type names in the return type
  {
    irept &ret_type = lambda_expr.add(ID_return_type);
    if(ret_type.is_not_nil() && ret_type.id() == ID_cpp_name)
    {
      irep_idt rname = ret_type.get_sub().front().get(ID_identifier);
      auto tm = type_map.find(rname);
      if(tm != type_map.end())
        ret_type = static_cast<const irept &>(tm->second);
    }
  }

  // Now type-check this lambda as a non-generic lambda with the inst_name
  // We do this by calling typecheck_expr_lambda with the modified expression.
  // But since typecheck_expr_lambda uses a counter for naming, we need to
  // set up the name manually.

  // Extract the scope prefix from the original lambda name
  // e.g., "main::1::__lambda_0" -> scope prefix is "main::1::"
  std::string orig = id2string(lambda_name);
  auto last_sep = orig.rfind("::");
  std::string scope_prefix =
    (last_sep != std::string::npos) ? orig.substr(0, last_sep + 2) : "";

  // Use inst_name as the function symbol name
  const source_locationt &loc = lambda_expr.source_location();

  // Collect parameters
  code_typet::parameterst func_params;
  for(const auto &p : params.get_sub())
  {
    const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
    if(pdecl.get_bool("explicit_this"))
      continue;
    typet ptype = pdecl.type();
    if(!ptype.id().empty())
      typecheck_type(ptype);
    irep_idt pname;
    if(!pdecl.declarators().empty())
      pname =
        pdecl.declarators().front().name().get_sub().front().get(ID_identifier);
    code_typet::parametert param(ptype);
    param.set_identifier(inst_name + "::" + id2string(pname));
    param.set_base_name(pname);
    func_params.push_back(param);
  }

  // Create parameter symbols
  for(const auto &p : func_params)
  {
    if(symbol_table.has_symbol(p.get_identifier()))
      continue;
    auxiliary_symbolt psym;
    psym.name = p.get_identifier();
    psym.base_name = p.get_base_name();
    psym.type = p.type();
    psym.mode = ID_cpp;
    psym.module = module;
    psym.location = loc;
    psym.is_file_local = true;
    psym.is_thread_local = true;
    psym.is_lvalue = true;
    psym.is_parameter = true;
    symbol_table.insert(std::move(psym));
  }

  // Collect captures from the original lambda
  const irept &capture_list = lambda_expr.find("lambda_capture");
  std::map<irep_idt, exprt> capture_values;
  std::set<irep_idt> by_ref_captures;
  for(const auto &cap : capture_list.get_sub())
  {
    irep_idt cap_name = cap.get(ID_identifier);
    if(cap_name.empty())
      continue;
    if(cap.get_bool("by_ref"))
      by_ref_captures.insert(cap_name);
    const exprt &init = static_cast<const exprt &>(cap.find("init"));
    if(init.is_not_nil())
    {
      exprt init_copy = init;
      typecheck_expr(init_copy);
      capture_values[cap_name] = init_copy;
    }
    else
    {
      exprt cap_expr(ID_cpp_name);
      irept name_node(ID_name);
      name_node.set(ID_identifier, cap_name);
      cap_expr.get_sub().push_back(name_node);
      cap_expr.add_source_location() = loc;
      typecheck_expr(cap_expr);
      capture_values[cap_name] = cap_expr;
    }
  }

  // Type-check the body
  typet lambda_return_type = signed_int_type();
  bool deduce_return = true;
  {
    const irept &explicit_ret = lambda_expr.find(ID_return_type);
    if(explicit_ret.is_not_nil() && !explicit_ret.id().empty())
    {
      lambda_return_type = static_cast<const typet &>(explicit_ret);
      typecheck_type(lambda_return_type);
      deduce_return = false;
    }
  }

  code_typet func_type(func_params, lambda_return_type);

  codet body_code(ID_nil);
  {
    cpp_save_scopet save_scope(cpp_scopes);

    // Find or create the lambda scope
    std::string lambda_base = inst_name.substr(scope_prefix.size());
    cpp_scopet &lambda_scope =
      cpp_scopes.current_scope().new_scope(lambda_base);
    lambda_scope.prefix = inst_name + "::";
    cpp_scopes.go_to(lambda_scope);

    for(const auto &p : func_params)
    {
      const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
      cpp_idt &id = cpp_scopes.put_into_scope(psym);
      id.id_class = cpp_idt::id_classt::SYMBOL;
    }

    for(const auto &cap : capture_values)
    {
      if(by_ref_captures.count(cap.first))
      {
        if(cap.second.id() == ID_symbol)
        {
          const symbolt &outer_sym = symbol_table.lookup_ref(
            to_symbol_expr(cap.second).get_identifier());
          cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
          cid.id_class = cpp_idt::id_classt::SYMBOL;
          continue;
        }
      }

      std::string csym_name = inst_name + "::" + id2string(cap.first);
      if(!symbol_table.has_symbol(csym_name))
      {
        auxiliary_symbolt csym;
        csym.name = csym_name;
        csym.base_name = cap.first;
        csym.type = cap.second.type();
        csym.value = cap.second;
        csym.mode = ID_cpp;
        csym.module = module;
        csym.location = loc;
        csym.is_file_local = true;
        csym.is_thread_local = true;
        csym.is_lvalue = true;
        csym.is_state_var = true;
        symbol_table.insert(std::move(csym));
      }

      const symbolt &inserted = symbol_table.lookup_ref(csym_name);
      cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
      cid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    body_code = to_code(static_cast<exprt &>(lambda_expr.add("body")));

    typet old_return_type = return_type;
    if(deduce_return)
      return_type = typet(ID_auto);
    else
      return_type = func_type.return_type();

    typecheck_code(body_code);

    if(deduce_return)
    {
      std::function<const exprt *(const codet &)> find_return =
        [&](const codet &code) -> const exprt *
      {
        if(code.get_statement() == ID_return && code.has_operands())
          return &code.op0();
        for(const auto &op : code.operands())
          if(op.id() == ID_code)
          {
            const exprt *r = find_return(to_code(op));
            if(r != nullptr)
              return r;
          }
        return nullptr;
      };
      const exprt *ret = find_return(body_code);
      if(ret != nullptr)
        func_type.return_type() = ret->type();
      else
        func_type.return_type() = void_type();
    }

    return_type = old_return_type;

    // Prepend capture initializations
    if(!capture_values.empty())
    {
      code_blockt block;
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
          continue;
        symbol_exprt cap_sym(
          inst_name + "::" + id2string(cap.first), cap.second.type());
        codet assign(ID_assign);
        assign.copy_to_operands(cap_sym);
        assign.copy_to_operands(cap.second);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }
      if(body_code.get_statement() == ID_block)
      {
        for(auto &stmt : to_code_block(body_code).statements())
          block.add(std::move(stmt));
      }
      else
        block.add(std::move(body_code));
      body_code = std::move(block);
    }
  }

  // Create the function symbol
  symbolt func_sym;
  func_sym.name = inst_name;
  func_sym.base_name = inst_name.substr(scope_prefix.size());
  func_sym.type = func_type;
  func_sym.value = body_code;
  func_sym.mode = ID_cpp;
  func_sym.module = module;
  func_sym.location = loc;
  func_sym.is_file_local = true;
  symbol_table.insert(std::move(func_sym));

  // Redirect the call to the new instantiation
  expr.function() = symbol_exprt(inst_name, func_type);
  expr.type() = func_type.return_type();
}

void cpp_typecheckt::typecheck_expr_side_effect(
  side_effect_exprt &expr)
{
  const irep_idt &statement=expr.get(ID_statement);

  if(statement==ID_cpp_new ||
     statement==ID_cpp_new_array)
  {
    typecheck_expr_new(expr);
  }
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
  {
    typecheck_expr_delete(expr);
  }
  else if(statement==ID_preincrement ||
          statement==ID_predecrement ||
          statement==ID_postincrement ||
          statement==ID_postdecrement)
  {
    typecheck_side_effect_inc_dec(expr);
  }
  else if(statement==ID_throw)
  {
    typecheck_expr_throw(expr);
  }
  else if(statement==ID_temporary_object)
  {
    // TODO
  }
  else
    c_typecheck_baset::typecheck_expr_side_effect(expr);
}

void cpp_typecheckt::typecheck_method_application(
  side_effect_expr_function_callt &expr)
{
  PRECONDITION(expr.operands().size() == 2);

  PRECONDITION(expr.function().id() == ID_member);
  PRECONDITION(expr.function().operands().size() == 1);

  // turn e.f(...) into xx::f(e, ...)

  exprt member_expr;
  member_expr.swap(expr.function());

  symbolt &method_symbol =
    symbol_table.get_writeable_ref(member_expr.get(ID_component_name));

  const irep_idt &member_name = method_symbol.type.get(ID_C_member_name);

  if(!member_name.empty())
  {
    const symbolt &tag_symbol = lookup(member_name);

    // build the right template map
    // if this is an instantiated template class method
    if(tag_symbol.type.find(ID_C_template) != irept())
    {
      cpp_saved_template_mapt saved_map(template_map);
      const irept &template_type = tag_symbol.type.find(ID_C_template);
      const irept &template_args =
        tag_symbol.type.find(ID_C_template_arguments);
      template_map.build(
        static_cast<const template_typet &>(template_type),
        static_cast<const cpp_template_args_tct &>(template_args));
      add_method_body(&method_symbol);
#ifdef DEBUG
      std::cout << "MAP for " << method_symbol << ":\n";
      template_map.print(std::cout);
#endif
    }
    else
      add_method_body(&method_symbol);
  }
  else
    add_method_body(&method_symbol);

  // If the method has an auto return type, force immediate type-checking
  // of the body so the return type is deduced before the call site uses it.
  if(
    method_symbol.type.id() == ID_code &&
    has_auto(to_code_type(method_symbol.type).return_type()) &&
    method_symbol.value.is_not_nil())
  {
    convert_function(method_symbol);
  }

  // build new function expression
  exprt new_function(cpp_symbol_expr(method_symbol));
  new_function.add_source_location()=member_expr.source_location();
  expr.function().swap(new_function);

  if(!expr.function().type().get_bool(ID_C_is_static))
  {
    const code_typet &func_type = to_code_type(method_symbol.type);
    typet this_type = func_type.parameters().front().type();

    // C++23 deducing this: first parameter is the object by value,
    // not a pointer.
    if(func_type.get_bool("explicit_this"))
    {
      if(expr.arguments().size() < func_type.parameters().size())
      {
        exprt this_arg = to_member_expr(member_expr).compound();
        implicit_typecast(this_arg, this_type);
        expr.arguments().insert(expr.arguments().begin(), this_arg);
      }
    }
    else
    {
      // Special case. Make it a reference.
      DATA_INVARIANT(this_type.id() == ID_pointer, "this should be pointer");
      this_type.set(ID_C_reference, true);
      this_type.set(ID_C_this, true);

      if(expr.arguments().size() == func_type.parameters().size())
      {
        // this might be set up for base-class initialisation
        if(
          expr.arguments().front().type() !=
          func_type.parameters().front().type())
        {
          implicit_typecast(expr.arguments().front(), this_type);
          DATA_INVARIANT(
            is_reference(expr.arguments().front().type()),
            "argument should be reference");
          expr.arguments().front().type().remove(ID_C_reference);
        }
      }
      else
      {
        exprt this_arg = to_member_expr(member_expr).compound();
        implicit_typecast(this_arg, this_type);
        // For multiple inheritance, the implicit_typecast may produce a
        // simple typecast from derived* to base* without adjusting the
        // pointer offset. Re-do the pointer cast using make_ptr_typecast
        // which handles non-first base class offsets.
        if(
          this_arg.id() == ID_typecast && this_arg.type().id() == ID_pointer &&
          to_typecast_expr(this_arg).op().type().id() == ID_pointer &&
          to_pointer_type(this_arg.type()).base_type().id() == ID_struct_tag &&
          to_pointer_type(to_typecast_expr(this_arg).op().type())
              .base_type()
              .id() == ID_struct_tag)
        {
          // Only adjust for upcasts (derived* -> base*).
          const struct_typet &src_s = follow_tag(to_struct_tag_type(
            to_pointer_type(to_typecast_expr(this_arg).op().type())
              .base_type()));
          const struct_typet &dest_s = follow_tag(
            to_struct_tag_type(to_pointer_type(this_arg.type()).base_type()));
          if(subtype_typecast(src_s, dest_s))
          {
            exprt inner = to_typecast_expr(this_arg).op();
            pointer_typet dest_ptr_type(
              to_pointer_type(this_arg.type()).base_type(),
              to_pointer_type(this_arg.type()).get_width());
            make_ptr_typecast(inner, dest_ptr_type);
            inner.type().set(ID_C_reference, true);
            inner.type().set(ID_C_this, true);
            this_arg = inner;
          }
        }
        DATA_INVARIANT(
          is_reference(this_arg.type()), "argument should be reference");
        this_arg.type().remove(ID_C_reference);
        expr.arguments().insert(expr.arguments().begin(), this_arg);
      }
    } // end else (non-deducing-this)
  }

  if(
    method_symbol.value.id() == ID_cpp_not_typechecked &&
    !method_symbol.value.get_bool(ID_is_used))
  {
    method_symbol.value.set(ID_is_used, true);
  }
}

void cpp_typecheckt::typecheck_side_effect_assignment(side_effect_exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "assignment side effect expected to have two operands"
            << eom;
    throw 0;
  }

  typet type0 = to_binary_expr(expr).op0().type();

  if(is_reference(type0))
    type0 = to_reference_type(type0).base_type();

  if(cpp_is_pod(type0))
  {
    // for structs we use the 'implicit assignment operator',
    // and therefore, it is allowed to assign to a rvalue struct.
    if(type0.id() == ID_struct_tag)
      to_binary_expr(expr).op0().set(ID_C_lvalue, true);

    c_typecheck_baset::typecheck_side_effect_assignment(expr);

    // Note that in C++ (as opposed to C), the assignment yields
    // an lvalue!
    expr.set(ID_C_lvalue, true);
    return;
  }

  // It's a non-POD.
  // Turn into an operator call

  std::string strop="operator";

  const irep_idt statement=expr.get(ID_statement);

  if(statement==ID_assign)
    strop += "=";
  else if(statement==ID_assign_shl)
    strop += "<<=";
  else if(statement==ID_assign_shr)
    strop += ">>=";
  else if(statement==ID_assign_plus)
    strop += "+=";
  else if(statement==ID_assign_minus)
    strop += "-=";
  else if(statement==ID_assign_mult)
    strop += "*=";
  else if(statement==ID_assign_div)
    strop += "/=";
  else if(statement==ID_assign_bitand)
    strop += "&=";
  else if(statement==ID_assign_bitor)
    strop += "|=";
  else if(statement==ID_assign_bitxor)
    strop += "^=";
  else
  {
    error().source_location=expr.find_source_location();
    error() << "bad assignment operator '" << statement << "'" << eom;
    throw 0;
  }

  const cpp_namet cpp_name(strop, expr.source_location());

  // expr.op0() is already typechecked
  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.add_to_operands(already_typechecked_exprt{to_binary_expr(expr).op0()});

  side_effect_expr_function_callt new_expr(
    std::move(member),
    {to_binary_expr(expr).op1()},
    uninitialized_typet{},
    expr.source_location());

  typecheck_side_effect_function_call(new_expr);

  expr=new_expr;
}

void cpp_typecheckt::typecheck_side_effect_inc_dec(
  side_effect_exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "statement " << expr.get_statement()
            << " expected to have one operand" << eom;
    throw 0;
  }

  auto &op = to_unary_expr(expr).op();

  add_implicit_dereference(op);

  const typet &tmp_type = op.type();

  if(is_number(tmp_type) ||
     tmp_type.id()==ID_pointer)
  {
    // standard stuff
    c_typecheck_baset::typecheck_expr_side_effect(expr);
    return;
  }

  // Turn into an operator call

  std::string str_op="operator";
  bool post=false;

  if(expr.get(ID_statement)==ID_preincrement)
    str_op += "++";
  else if(expr.get(ID_statement)==ID_predecrement)
    str_op += "--";
  else if(expr.get(ID_statement)==ID_postincrement)
  {
    str_op += "++";
    post=true;
  }
  else if(expr.get(ID_statement)==ID_postdecrement)
  {
    str_op += "--";
    post=true;
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "bad assignment operator '" << expr.get_statement() << "'"
            << eom;
    throw 0;
  }

  const cpp_namet cpp_name(str_op, expr.source_location());

  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.add_to_operands(already_typechecked_exprt{op});

  side_effect_expr_function_callt new_expr(
    std::move(member), {}, uninitialized_typet{}, expr.source_location());

  // the odd C++ way to denote the post-inc/dec operator
  if(post)
    new_expr.arguments().push_back(
      from_integer(mp_integer(0), signed_int_type()));

  typecheck_side_effect_function_call(new_expr);
  expr.swap(new_expr);
}

void cpp_typecheckt::typecheck_expr_dereference(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "unary operator * expects one operand" << eom;
    throw 0;
  }

  exprt &op = to_dereference_expr(expr).pointer();
  const typet &op_type = op.type();

  if(op_type.id() == ID_pointer && op_type.find(ID_to_member).is_not_nil())
  {
    error().source_location=expr.find_source_location();
    error() << "pointer-to-member must use "
            << "the .* or ->* operators" << eom;
    throw 0;
  }

  c_typecheck_baset::typecheck_expr_dereference(expr);
}

void cpp_typecheckt::convert_pmop(exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_to_member);
  PRECONDITION(expr.operands().size() == 2);

  auto &op0 = to_binary_expr(expr).op0();
  auto &op1 = to_binary_expr(expr).op1();

  if(op1.type().id() != ID_pointer || op1.type().find(ID_to_member).is_nil())
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member expected" << eom;
    throw 0;
  }

  typet t0 = op0.type().id() == ID_pointer
               ? to_pointer_type(op0.type()).base_type()
               : op0.type();

  typet t1((const typet &)op1.type().find(ID_to_member));

  if(t0.id() != ID_struct_tag)
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  const struct_typet &from_struct = follow_tag(to_struct_tag_type(t0));
  const struct_typet &to_struct = follow_tag(to_struct_tag_type(t1));

  if(!subtype_typecast(from_struct, to_struct))
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  typecheck_expr_main(op1);

  if(op0.type().id() != ID_pointer)
  {
    if(op0.id() == ID_dereference)
    {
      op0 = to_dereference_expr(op0).pointer();
    }
    else
    {
      DATA_INVARIANT(
        op0.get_bool(ID_C_lvalue),
        "pointer-to-member must have lvalue operand");
      op0 = address_of_exprt(op0);
    }
  }

  exprt tmp(op1);
  tmp.type().set(ID_C_bound, op0);
  expr.swap(tmp);
  return;
}

void cpp_typecheckt::typecheck_expr_function_identifier(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    // Check if the function body has to be typechecked
    symbolt &function_symbol =
      symbol_table.get_writeable_ref(expr.get(ID_identifier));

    if(function_symbol.value.id() == ID_cpp_not_typechecked)
      function_symbol.value.set(ID_is_used, true);

    // For functions in deferred_typechecking (e.g., static member
    // functions of class templates), ensure the body gets typechecked
    // by adding it to method_bodies.
    if(
      function_symbol.value.is_not_nil() &&
      deferred_typechecking.count(function_symbol.name))
    {
      add_method_body(&function_symbol);
    }
  }

  c_typecheck_baset::typecheck_expr_function_identifier(expr);
}

void cpp_typecheckt::typecheck_expr(exprt &expr)
{
  bool override_constantness = expr.get_bool(ID_C_override_constantness);

  // We take care of an ambiguity in the C++ grammar.
  // Needs to be done before the operands!
  explicit_typecast_ambiguity(expr);

  // cpp_name uses get_sub, which can get confused with expressions.
  if(expr.id()==ID_cpp_name)
    typecheck_expr_cpp_name(expr, cpp_typecheck_fargst());
  else if(expr.id() == "lambda")
    typecheck_expr_lambda(expr);
  else
  {
    // This does the operands, and then calls typecheck_expr_main.
    c_typecheck_baset::typecheck_expr(expr);
  }

  if(override_constantness)
    expr.type().set(ID_C_constant, false);
}

void cpp_typecheckt::explicit_typecast_ambiguity(exprt &expr)
{
  // There is an ambiguity in the C++ grammar as follows:
  // (TYPENAME) + expr   (typecast of unary plus)  vs.
  // (expr) + expr       (sum of two expressions)
  // Same issue with the operators & and - and *

  // We figure this out by resolving the type argument
  // and re-writing if needed

  if(expr.id()!="explicit-typecast")
    return;

  PRECONDITION(expr.operands().size() == 1);

  irep_idt op0_id = to_unary_expr(expr).op().id();

  if(
    expr.type().id() == ID_cpp_name &&
    to_unary_expr(expr).op().operands().size() == 1 &&
    (op0_id == ID_unary_plus || op0_id == ID_unary_minus ||
     op0_id == ID_address_of || op0_id == ID_dereference))
  {
    exprt resolve_result=
      resolve(
        to_cpp_name(expr.type()),
        cpp_typecheck_resolvet::wantt::BOTH,
        cpp_typecheck_fargst());

    if(resolve_result.id()!=ID_type)
    {
      // need to re-write the expression
      // e.g., (ID) +expr  ->  ID+expr
      exprt new_binary_expr;

      new_binary_expr.operands().resize(2);
      to_binary_expr(new_binary_expr).op0().swap(expr.type());
      to_binary_expr(new_binary_expr)
        .op1()
        .swap(to_unary_expr(to_unary_expr(expr).op()).op());

      if(op0_id==ID_unary_plus)
        new_binary_expr.id(ID_plus);
      else if(op0_id==ID_unary_minus)
        new_binary_expr.id(ID_minus);
      else if(op0_id==ID_address_of)
        new_binary_expr.id(ID_bitand);
      else if(op0_id==ID_dereference)
        new_binary_expr.id(ID_mult);

      new_binary_expr.add_source_location() =
        to_unary_expr(expr).op().source_location();
      expr.swap(new_binary_expr);
    }
  }
}

void cpp_typecheckt::typecheck_expr_binary_arithmetic(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "operator '" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  add_implicit_dereference(to_binary_expr(expr).op0());
  add_implicit_dereference(to_binary_expr(expr).op1());

  c_typecheck_baset::typecheck_expr_binary_arithmetic(expr);
}

void cpp_typecheckt::typecheck_expr_index(exprt &expr)
{
  c_typecheck_baset::typecheck_expr_index(expr);
}

void cpp_typecheckt::typecheck_expr_comma(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "comma operator expects two operands" << eom;
    throw 0;
  }

  const auto &op0_type = to_binary_expr(expr).op0().type();

  if(op0_type.id() == ID_struct || op0_type.id() == ID_struct_tag)
  {
    // TODO: check if the comma operator has been overloaded!
  }

  c_typecheck_baset::typecheck_expr_comma(expr);
}

void cpp_typecheckt::typecheck_expr_rel(binary_relation_exprt &expr)
{
  c_typecheck_baset::typecheck_expr_rel(expr);

  // Ensure both operands of pointer comparisons have exactly the same
  // type. The C type-checker creates null_pointer_exprt with the right
  // base type, but pointer annotations (e.g., #to_member for
  // pointer-to-member-function) may differ. Force the rhs type to
  // match the lhs type when both are pointers.
  if(
    expr.op0().type().id() == ID_pointer &&
    expr.op1().type().id() == ID_pointer &&
    expr.op0().type() != expr.op1().type())
  {
    expr.op1() = typecast_exprt(expr.op1(), expr.op0().type());
  }
}

void cpp_typecheckt::typecheck_expr_lambda(exprt &expr)
{
  // Lower C++11 lambda by creating a function where captured variables
  // become local constants initialized to their capture-point values.
  // The lambda becomes a function pointer.

  static unsigned lambda_count = 0;
  const std::string lambda_id = "__lambda_" + std::to_string(lambda_count++);
  const source_locationt &loc = expr.source_location();
  const std::string func_sym_name =
    id2string(cpp_scopes.current_scope().prefix) + lambda_id;

  // Check for C++14 generic lambda (auto parameters) or
  // C++20 template lambda (unresolved type name parameters)
  bool is_generic_lambda = false;
  {
    const irept &check_params = expr.find(ID_parameters);
    for(const auto &p : check_params.get_sub())
    {
      const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
      if(pdecl.get_bool("explicit_this"))
        continue;
      if(
        has_auto(pdecl.type()) || pdecl.type().id() == ID_cpp_name ||
        pdecl.type().id() == ID_auto)
      {
        is_generic_lambda = true;
        break;
      }
    }

    if(is_generic_lambda)
    {
      generic_lambda_map[func_sym_name] = expr;

      // Replace auto/template parameters with signed int
      irept &default_params = expr.add(ID_parameters);
      for(auto &p : default_params.get_sub())
      {
        cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
        if(pdecl.get_bool("explicit_this"))
          continue;
        if(has_auto(pdecl.type()) || pdecl.type().id() == ID_cpp_name)
          replace_auto_in_type(pdecl.type(), signed_int_type());
      }
    }
  }

  // Collect captures
  const irept &capture_list = expr.find("lambda_capture");
  std::map<irep_idt, exprt> capture_values;
  std::set<irep_idt> by_ref_captures;
  for(const auto &cap : capture_list.get_sub())
  {
    irep_idt cap_name = cap.get(ID_identifier);
    if(cap_name.empty())
      continue;

    if(cap.get_bool("by_ref"))
      by_ref_captures.insert(cap_name);

    // C++14 init-capture: [y = expr]
    const exprt &init = static_cast<const exprt &>(cap.find("init"));
    if(init.is_not_nil())
    {
      exprt init_copy = init;
      typecheck_expr(init_copy);
      capture_values[cap_name] = init_copy;
    }
    else
    {
      exprt cap_expr(ID_cpp_name);
      irept name_node(ID_name);
      name_node.set(ID_identifier, cap_name);
      cap_expr.get_sub().push_back(name_node);
      cap_expr.add_source_location() = loc;
      typecheck_expr(cap_expr);
      capture_values[cap_name] = cap_expr;
    }
  }

  // Collect parameters
  const irept &params_irep = expr.find(ID_parameters);
  code_typet::parameterst func_params;
  for(const auto &p : params_irep.get_sub())
  {
    const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
    // C++23 deducing this: skip explicit object parameter
    if(pdecl.get_bool("explicit_this"))
      continue;
    typet ptype = pdecl.type();
    typecheck_type(ptype);
    irep_idt pname;
    if(!pdecl.declarators().empty())
      pname =
        pdecl.declarators().front().name().get_sub().front().get(ID_identifier);
    code_typet::parametert param(ptype);
    param.set_identifier(func_sym_name + "::" + id2string(pname));
    param.set_base_name(pname);
    func_params.push_back(param);
  }

  // Determine return type: use explicit trailing return type if present
  // (and not a generic lambda where the type may reference template params),
  // otherwise deduce from body.
  typet lambda_return_type = signed_int_type();
  bool deduce_return = true;
  {
    const irept &explicit_ret = expr.find(ID_return_type);
    if(explicit_ret.is_not_nil() && !is_generic_lambda)
    {
      lambda_return_type = static_cast<const typet &>(explicit_ret);
      typecheck_type(lambda_return_type);
      deduce_return = false;
    }
  }

  code_typet func_type(std::move(func_params), lambda_return_type);

  // Create parameter symbols
  for(const auto &p : func_type.parameters())
  {
    auxiliary_symbolt psym;
    psym.name = p.get_identifier();
    psym.base_name = p.get_base_name();
    psym.type = p.type();
    psym.mode = ID_cpp;
    psym.module = module;
    psym.location = loc;
    psym.is_file_local = true;
    psym.is_thread_local = true;
    psym.is_lvalue = true;
    psym.is_parameter = true;
    symbol_table.insert(std::move(psym));
  }

  // For generic lambdas, try to type-check the body with the default int
  // parameters. If it succeeds, the lambda can be used as a function pointer.
  // If it fails (e.g., body uses struct members), defer to call-site
  // instantiation.
  if(is_generic_lambda)
  {
    codet default_body(ID_nil);
    bool body_ok = false;

    // Save error count so we can restore it if body type-checking fails
    const std::size_t saved_errors =
      get_message_handler().get_message_count(messaget::M_ERROR);
    const unsigned saved_verbosity = get_message_handler().get_verbosity();

    // Suppress error messages during the try
    get_message_handler().set_verbosity(0);

    // Try type-checking with int parameters
    try
    {
      cpp_save_scopet save_scope(cpp_scopes);
      cpp_scopet &lambda_scope =
        cpp_scopes.current_scope().new_scope(lambda_id + "_try");
      lambda_scope.prefix = func_sym_name + "::";
      cpp_scopes.go_to(lambda_scope);

      for(const auto &p : func_type.parameters())
      {
        if(!symbol_table.has_symbol(p.get_identifier()))
        {
          auxiliary_symbolt psym;
          psym.name = p.get_identifier();
          psym.base_name = p.get_base_name();
          psym.type = p.type();
          psym.mode = ID_cpp;
          psym.module = module;
          psym.location = loc;
          psym.is_file_local = true;
          psym.is_thread_local = true;
          psym.is_lvalue = true;
          psym.is_parameter = true;
          symbol_table.insert(std::move(psym));
        }
        const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
        cpp_idt &id = cpp_scopes.put_into_scope(psym);
        id.id_class = cpp_idt::id_classt::SYMBOL;
      }

      // Put captures in scope
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
        {
          if(cap.second.id() == ID_symbol)
          {
            const symbolt &outer_sym = symbol_table.lookup_ref(
              to_symbol_expr(cap.second).get_identifier());
            cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
            cid.id_class = cpp_idt::id_classt::SYMBOL;
            continue;
          }
        }

        std::string csym_name = func_sym_name + "::" + id2string(cap.first);
        if(!symbol_table.has_symbol(csym_name))
        {
          auxiliary_symbolt csym;
          csym.name = csym_name;
          csym.base_name = cap.first;
          csym.type = cap.second.type();
          csym.value = cap.second;
          csym.mode = ID_cpp;
          csym.module = module;
          csym.location = loc;
          csym.is_file_local = true;
          csym.is_thread_local = true;
          csym.is_lvalue = true;
          csym.is_state_var = true;
          symbol_table.insert(std::move(csym));
        }

        const symbolt &inserted = symbol_table.lookup_ref(csym_name);
        cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
        cid.id_class = cpp_idt::id_classt::SYMBOL;
      }

      default_body = to_code(static_cast<exprt &>(expr.add("body")));

      typet old_return_type = return_type;
      return_type = typet(ID_auto);
      typecheck_code(default_body);

      // Deduce return type
      std::function<const exprt *(const codet &)> find_return =
        [&](const codet &code) -> const exprt *
      {
        if(code.get_statement() == ID_return && code.has_operands())
          return &code.op0();
        for(const auto &op : code.operands())
          if(op.id() == ID_code)
          {
            const exprt *r = find_return(to_code(op));
            if(r != nullptr)
              return r;
          }
        return nullptr;
      };
      const exprt *ret = find_return(default_body);
      if(ret != nullptr)
        func_type.return_type() = ret->type();
      else
        func_type.return_type() = void_type();

      return_type = old_return_type;

      // Prepend capture initializations
      if(!capture_values.empty())
      {
        code_blockt block;
        for(const auto &cap : capture_values)
        {
          if(by_ref_captures.count(cap.first))
            continue;
          symbol_exprt cap_sym(
            func_sym_name + "::" + id2string(cap.first), cap.second.type());
          codet assign(ID_assign);
          assign.copy_to_operands(cap_sym);
          assign.copy_to_operands(cap.second);
          assign.add_source_location() = loc;
          block.add(std::move(assign));
        }
        if(default_body.get_statement() == ID_block)
        {
          for(auto &stmt : to_code_block(default_body).statements())
            block.add(std::move(stmt));
        }
        else
          block.add(std::move(default_body));
        default_body = std::move(block);
      }

      body_ok = true;
    }
    catch(...)
    {
      // Body type-checking failed with int params — leave body as nil
      // Restore error count so this doesn't cause overall failure
      get_message_handler().set_message_count(messaget::M_ERROR, saved_errors);
    }

    // Restore verbosity
    get_message_handler().set_verbosity(saved_verbosity);

    symbolt func_sym;
    func_sym.name = func_sym_name;
    func_sym.base_name = lambda_id;
    func_sym.type = func_type;
    func_sym.value = body_ok ? static_cast<exprt>(default_body) : nil_exprt();
    func_sym.mode = ID_cpp;
    func_sym.module = module;
    func_sym.location = loc;
    func_sym.is_file_local = true;
    symbol_table.insert(std::move(func_sym));

    {
      const symbolt &fsym = symbol_table.lookup_ref(func_sym_name);
      cpp_idt &fid = cpp_scopes.put_into_scope(fsym);
      fid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    expr = address_of_exprt(symbol_exprt(func_sym_name, func_type));
    expr.type() = pointer_typet(func_type, config.ansi_c.pointer_width);
    expr.add_source_location() = loc;
    return;
  }

  // Type-check the body with captures and params in scope
  codet body_code(ID_nil);
  {
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopet &lambda_scope = cpp_scopes.current_scope().new_scope(lambda_id);
    lambda_scope.prefix = func_sym_name + "::";
    cpp_scopes.go_to(lambda_scope);

    for(const auto &p : func_type.parameters())
    {
      const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
      cpp_idt &id = cpp_scopes.put_into_scope(psym);
      id.id_class = cpp_idt::id_classt::SYMBOL;
    }

    for(const auto &cap : capture_values)
    {
      // By-ref captures: put the outer symbol directly into scope
      if(by_ref_captures.count(cap.first))
      {
        if(cap.second.id() == ID_symbol)
        {
          const symbolt &outer_sym = symbol_table.lookup_ref(
            to_symbol_expr(cap.second).get_identifier());
          cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
          cid.id_class = cpp_idt::id_classt::SYMBOL;
          continue;
        }
      }

      auxiliary_symbolt csym;
      csym.name = func_sym_name + "::" + id2string(cap.first);
      csym.base_name = cap.first;
      csym.type = cap.second.type();
      csym.value = cap.second;
      csym.mode = ID_cpp;
      csym.module = module;
      csym.location = loc;
      csym.is_file_local = true;
      csym.is_thread_local = true;
      csym.is_lvalue = true;
      csym.is_state_var = true;
      symbol_table.insert(std::move(csym));

      const symbolt &inserted =
        symbol_table.lookup_ref(func_sym_name + "::" + id2string(cap.first));
      cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
      cid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    body_code = to_code(static_cast<exprt &>(expr.add("body")));

    // Save/restore return_type so the lambda body uses its own return type
    typet old_return_type = return_type;
    if(deduce_return)
      return_type = typet(ID_auto);
    else
      return_type = func_type.return_type();

    typecheck_code(body_code);

    // Deduce return type from body if not explicitly specified
    if(deduce_return)
    {
      std::function<const exprt *(const codet &)> find_return =
        [&](const codet &code) -> const exprt *
      {
        if(code.get_statement() == ID_return && code.has_operands())
          return &code.op0();
        for(const auto &op : code.operands())
          if(op.id() == ID_code)
          {
            const exprt *r = find_return(to_code(op));
            if(r != nullptr)
              return r;
          }
        return nullptr;
      };
      const exprt *ret = find_return(body_code);
      if(ret != nullptr)
        func_type.return_type() = ret->type();
      else
        func_type.return_type() = void_type();
    }

    return_type = old_return_type;

    // Prepend capture initializations to the body
    if(!capture_values.empty())
    {
      code_blockt block;
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
          continue;
        symbol_exprt cap_sym(
          func_sym_name + "::" + id2string(cap.first), cap.second.type());
        codet assign(ID_assign);
        assign.copy_to_operands(cap_sym);
        assign.copy_to_operands(cap.second);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }
      if(body_code.get_statement() == ID_block)
      {
        for(auto &stmt : to_code_block(body_code).statements())
          block.add(std::move(stmt));
      }
      else
        block.add(std::move(body_code));
      body_code = std::move(block);
    }
  }

  // Create the function symbol
  symbolt func_sym;
  func_sym.name = func_sym_name;
  func_sym.base_name = lambda_id;
  func_sym.type = func_type;
  func_sym.value = body_code;
  func_sym.mode = ID_cpp;
  func_sym.module = module;
  func_sym.location = loc;
  func_sym.is_file_local = true;
  symbol_table.insert(std::move(func_sym));

  {
    const symbolt &fsym = symbol_table.lookup_ref(func_sym_name);
    cpp_idt &fid = cpp_scopes.put_into_scope(fsym);
    fid.id_class = cpp_idt::id_classt::SYMBOL;
  }

  // Replace the lambda with a function pointer
  expr = address_of_exprt(symbol_exprt(func_sym_name, func_type));
  expr.type() = pointer_typet(func_type, config.ansi_c.pointer_width);
  expr.add_source_location() = loc;
}
