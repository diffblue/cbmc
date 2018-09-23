/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/pointer_offset_size.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_exception_id.h"
#include "cpp_type2name.h"
#include "expr2cpp.h"

bool cpp_typecheckt::find_parent(
  const symbolt &symb,
  const irep_idt &base_name,
  irep_idt &identifier)
{
  forall_irep(bit, symb.type.find(ID_bases).get_sub())
  {
    if(lookup(bit->find(ID_type).get(ID_identifier)).base_name == base_name)
    {
      identifier=bit->find(ID_type).get(ID_identifier);
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
  else if(expr.id()=="pointer-to-member")
    convert_pmop(expr);
  else if(expr.id() == ID_new_object)
  {
  }
  else if(operator_is_overloaded(expr))
  {
  }
  else if(expr.id()=="explicit-typecast")
    typecheck_expr_explicit_typecast(expr);
  else if(expr.id()=="explicit-constructor-call")
    typecheck_expr_explicit_constructor_call(expr);
  else if(expr.is_nil())
  {
#ifdef DEBUG
    std::cerr << "E: " << expr.pretty() << '\n';
    std::cerr << "cpp_typecheckt::typecheck_expr_main got nil\n";
#endif
    UNREACHABLE;
  }
  else if(expr.id()==ID_code)
  {
#ifdef DEBUG
    std::cerr << "E: " << expr.pretty() << '\n';
    std::cerr << "cpp_typecheckt::typecheck_expr_main got code\n";
#endif
    UNREACHABLE;
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

    base = follow(base);
    deriv = follow(deriv);

    if(base.id()!=ID_struct || deriv.id()!=ID_struct)
      expr=false_exprt();
    else
    {
      irep_idt base_name=base.get(ID_name);
      const class_typet &class_type=to_class_type(deriv);

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
    expr.type()=symbol_typet("tag-_GUID");
    follow(expr.type());
    expr.set(ID_C_lvalue, true);
  }
  else if(expr.id()==ID_noexcept)
  {
    // TODO
    expr=false_exprt();
  }
  else if(expr.id()==ID_initializer_list)
  {
    expr.type().id(ID_initializer_list);
  }
  else
    c_typecheck_baset::typecheck_expr_main(expr);
}

void cpp_typecheckt::typecheck_expr_trinary(if_exprt &expr)
{
  assert(expr.operands().size()==3);

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
        error() << "error: lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id()==ID_array)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_array_to_pointer(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "error: array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id()==ID_code)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_function_to_pointer(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "error: function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().get_bool(ID_C_lvalue))
    {
      exprt e2(expr.op2());
      if(!standard_conversion_lvalue_to_rvalue(e2, expr.op2()))
      {
        error().source_location=e2.find_source_location();
        error() << "error: lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id()==ID_array)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_array_to_pointer(e2, expr.op2()))
      {
        error().source_location=e2.find_source_location();
        error() << "error: array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id()==ID_code)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_function_to_pointer(e2, expr.op2()))
      {
        error().source_location=expr.find_source_location();
        error() << "error: function to pointer conversion" << eom;
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
      expr.type()=empty_typet();
    else
    {
      error().source_location=expr.find_source_location();
      error() << "error: bad types for operands" << eom;
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
    }
    else if(implicit_conversion_sequence(expr.op2(), expr.op1().type(), e2))
    {
      expr.type()=e2.type();
      expr.op2().swap(e2);
    }
    else if(expr.op1().type().id()==ID_array &&
            expr.op2().type().id()==ID_array &&
            expr.op1().type().subtype() == expr.op2().type().subtype())
    {
      // array-to-pointer conversion

      index_exprt index1;
      index1.array()=expr.op1();
      index1.index()=from_integer(0, index_type());
      index1.type()=expr.op1().type().subtype();

      index_exprt index2;
      index2.array()=expr.op2();
      index2.index()=from_integer(0, index_type());
      index2.type()=expr.op2().type().subtype();

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
      error() << "error: types are incompatible.\n"
              << "I got `" << type2cpp(expr.op1().type(), *this)
              << "' and `" << type2cpp(expr.op2().type(), *this)
              << "'." << eom;
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

      if(type.subtype().id()==ID_cpp_name)
      {
        cpp_typecheck_fargst fargs;

        exprt symbol_expr=resolve(
          to_cpp_name(static_cast<const irept &>(type.subtype())),
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
    add_implicit_dereference(expr.op0());

    // is operator-> overloaded?
    if(expr.op0().type().id() != ID_pointer)
    {
      std::string op_name="operator->";

      // turn this into a function call
      side_effect_expr_function_callt function_call;
      function_call.arguments().reserve(expr.operands().size());
      function_call.add_source_location()=expr.source_location();

      // first do function/operator
      cpp_namet cpp_name;
      cpp_name.get_sub().push_back(irept(ID_name));
      cpp_name.get_sub().back().set(ID_identifier, op_name);
      cpp_name.get_sub().back().add(ID_C_source_location)=
        expr.source_location();

      function_call.function()=
        static_cast<const exprt &>(
          static_cast<const irept &>(cpp_name));

      // now do the argument
      function_call.arguments().push_back(expr.op0());
      typecheck_side_effect_function_call(function_call);

      exprt tmp(ID_already_typechecked);
      tmp.copy_to_operands(function_call);
      function_call.swap(tmp);

      expr.op0().swap(function_call);
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

  forall_operands(it, expr)
  {
    typet t=follow(it->type());

    if(is_reference(t))
      t=t.subtype();

    if(t.id()==ID_struct ||
       t.id() == ID_incomplete_struct ||
       t.id()==ID_union ||
       t.id()==ID_c_enum || t.id() == ID_c_enum_tag)
      return true;
  }

  return false;
}

struct operator_entryt
{
  const irep_idt id;
  const char *op_name;
} const operators[] =
{
  { ID_plus, "+" },
  { ID_minus, "-" },
  { ID_mult, "*" },
  { ID_div, "/" },
  { ID_bitnot, "~" },
  { ID_bitand, "&" },
  { ID_bitor, "|" },
  { ID_bitxor, "^" },
  { ID_not, "!" },
  { ID_unary_minus, "-" },
  { ID_and, "&&" },
  { ID_or, "||" },
  { ID_not, "!" },
  { ID_index, "[]" },
  { ID_equal, "==" },
  { ID_lt, "<"},
  { ID_le, "<="},
  { ID_gt, ">"},
  { ID_ge, ">="},
  { ID_shl, "<<"},
  { ID_shr, ">>"},
  { ID_notequal, "!=" },
  { ID_dereference, "*" },
  { ID_ptrmember, "->" },
  { irep_idt(), nullptr }
};

bool cpp_typecheckt::operator_is_overloaded(exprt &expr)
{
  // Check argument types first.
  // At least one struct/enum operand is required.

  if(!overloadable(expr))
    return false;
  else if(expr.id()==ID_dereference &&
          expr.get_bool(ID_C_implicit))
    return false;

  assert(expr.operands().size()>=1);

  if(expr.id()=="explicit-typecast")
  {
    // the cast operator can be overloaded

    typet t=expr.type();
    typecheck_type(t);
    std::string op_name=std::string("operator")+"("+cpp_type2name(t)+")";

    // turn this into a function call
    side_effect_expr_function_callt function_call;
    function_call.arguments().reserve(expr.operands().size());
    function_call.add_source_location()=expr.source_location();

    cpp_namet cpp_name;
    cpp_name.get_sub().push_back(irept(ID_name));
    cpp_name.get_sub().back().set(ID_identifier, op_name);
    cpp_name.get_sub().back().add(ID_C_source_location)=expr.source_location();

    // See if the struct declares the cast operator as a member
    bool found_in_struct=false;
    assert(!expr.operands().empty());
    typet t0(follow(expr.op0().type()));

    if(t0.id()==ID_struct)
    {
      for(const auto &c : to_struct_type(t0).components())
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

    {
      exprt member(ID_member);
      member.add(ID_component_cpp_name)= cpp_name;

      exprt tmp(ID_already_typechecked);
      tmp.copy_to_operands(expr.op0());
      member.copy_to_operands(tmp);

      function_call.function()=member;
    }

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
      exprt tmp(ID_already_typechecked);
      tmp.move_to_operands(function_call);
      expr.op0().swap(tmp);
      typecheck_expr(expr);
      return true;
    }

    expr.swap(function_call);
    return true;
  }

  for(const operator_entryt *e=operators;
      !e->id.empty();
      e++)
    if(expr.id()==e->id)
    {
      if(expr.id()==ID_dereference)
        assert(!expr.get_bool(ID_C_implicit));

      std::string op_name=std::string("operator")+e->op_name;

      // first do function/operator
      cpp_namet cpp_name;
      cpp_name.get_sub().push_back(irept(ID_name));
      cpp_name.get_sub().back().set(ID_identifier, op_name);
      cpp_name.get_sub().back().add(ID_C_source_location)=
        expr.source_location();

      // turn this into a function call
      side_effect_expr_function_callt function_call;
      function_call.arguments().reserve(expr.operands().size());
      function_call.add_source_location()=expr.source_location();

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
      if(
        expr.op0().type().id() == ID_symbol_type &&
        follow(expr.op0().type()).id() == ID_struct)
      {
        const irep_idt &struct_identifier=
          expr.op0().type().get(ID_identifier);

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
          {
            exprt member(ID_member);
            member.add(ID_component_cpp_name)=cpp_name;

            exprt tmp(ID_already_typechecked);
            tmp.copy_to_operands(expr.op0());
            member.copy_to_operands(tmp);

            function_call.function()=member;
          }

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
          function_call.function()=
            static_cast<const exprt &>(
              static_cast<const irept &>(cpp_name));

          // now do arguments
          forall_operands(it, expr)
            function_call.arguments().push_back(*it);

          typecheck_side_effect_function_call(function_call);

          if(expr.id()==ID_ptrmember)
          {
            add_implicit_dereference(function_call);
            exprt tmp(ID_already_typechecked);
            tmp.move_to_operands(function_call);
            expr.op0()=tmp;
            typecheck_expr(expr);
            return true;
          }

          expr=function_call;

          return true;
        }
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

  exprt &op=expr.op0();

  if(!op.get_bool(ID_C_lvalue) && expr.type().id()==ID_code)
  {
    error().source_location=expr.source_location();
    error() << "expr not an lvalue" << eom;
    throw 0;
  }

  if(expr.op0().type().id()==ID_code)
  {
    // we take the address of the method.
    assert(expr.op0().id()==ID_member);
    exprt symb=cpp_symbol_expr(lookup(expr.op0().get(ID_component_name)));
    address_of_exprt address(symb, pointer_type(symb.type()));
    address.set(ID_C_implicit, true);
    expr.op0().swap(address);
  }

  if(expr.op0().id()==ID_address_of &&
     expr.op0().get_bool(ID_C_implicit))
  {
    // must be the address of a function
    code_typet &code_type=to_code_type(op.type().subtype());

    code_typet::parameterst &args=code_type.parameters();
    if(args.size() > 0 && args[0].get(ID_C_base_name)==ID_this)
    {
      // it's a pointer to member function
      const symbol_typet symbol(code_type.get(ID_C_member_name));
      expr.op0().type().add("to-member")=symbol;

      if(code_type.get_bool(ID_C_is_virtual))
      {
        error().source_location=expr.source_location();
        error() << "error: pointers to virtual methods"
                << " are currently not implemented" << eom;
        throw 0;
      }
    }
  }
  else if(
    expr.op0().id() == ID_ptrmember && expr.op0().op0().id() == "cpp-this")
  {
    expr.type() = pointer_type(expr.op0().type());
    expr.type().add("to-member") = expr.op0().op0().type().subtype();
    return;
  }

  // the C front end does not know about references
  const bool is_ref=is_reference(expr.type());
  c_typecheck_baset::typecheck_expr_address_of(expr);
  if(is_ref)
    expr.type()=reference_type(expr.type().subtype());
}

void cpp_typecheckt::typecheck_expr_throw(exprt &expr)
{
  // these are of type void
  expr.type()=empty_typet();

  assert(expr.operands().size()==1 ||
         expr.operands().empty());

  if(expr.operands().size()==1)
  {
    // nothing really to do; one can throw _almost_ anything
    const typet &exception_type=expr.op0().type();

    if(follow(exception_type).id()==ID_empty)
    {
      error().source_location=expr.op0().find_source_location();
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
    // first typecheck subtype
    typecheck_type(expr.type().subtype());

    // typecheck the size
    exprt &size=to_array_type(expr.type()).size();
    typecheck_expr(size);

    bool size_is_unsigned=(size.type().id()==ID_unsignedbv);
    typet integer_type(size_is_unsigned?ID_unsignedbv:ID_signedbv);
    integer_type.set(ID_width, config.ansi_c.int_width);
    implicit_typecast(size, integer_type);

    expr.set(ID_statement, ID_cpp_new_array);

    // save the size expression
    expr.set(ID_size, to_array_type(expr.type()).size());

    // new actually returns a pointer, not an array
    pointer_typet ptr_type=
      pointer_type(expr.type().subtype());
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

  exprt object_expr(ID_new_object, expr.type().subtype());
  object_expr.set(ID_C_lvalue, true);

  {
    exprt tmp(ID_already_typechecked);
    tmp.move_to_operands(object_expr);
    object_expr.swap(tmp);
  }

  // not yet typechecked-stuff
  exprt &initializer=static_cast<exprt &>(expr.add(ID_initializer));

  // arrays must not have an initializer
  if(!initializer.operands().empty() &&
     expr.get(ID_statement)==ID_cpp_new_array)
  {
    error().source_location=expr.op0().find_source_location();
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

  exprt &sizeof_expr=static_cast<exprt &>(expr.add(ID_sizeof));
  sizeof_expr=size_of_expr(expr.type().subtype(), *this);
  sizeof_expr.add(ID_C_c_sizeof_type)=expr.type().subtype();
}

static exprt collect_comma_expression(const exprt &src)
{
  exprt result;

  if(src.id()==ID_comma)
  {
    assert(src.operands().size()==2);
    result=collect_comma_expression(src.op0());
    result.copy_to_operands(src.op1());
  }
  else
    result.copy_to_operands(src);

  return result;
}

void cpp_typecheckt::typecheck_expr_explicit_typecast(exprt &expr)
{
  // these can have 0 or 1 arguments

  if(expr.operands().empty())
  {
    // Default value, e.g., int()
    typecheck_type(expr.type());
    exprt new_expr=
      ::zero_initializer(
        expr.type(),
        expr.find_source_location(),
        *this,
        get_message_handler());

    new_expr.add_source_location()=expr.source_location();
    expr=new_expr;
  }
  else if(expr.operands().size()==1)
  {
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
        side_effect_expr_function_callt f_call;

        f_call.add_source_location()=expr.source_location();
        f_call.function().swap(expr.type());
        f_call.arguments()=collect_comma_expression(expr.op0()).operands();

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
    if(expr.op0().id()==ID_initializer_list)
    {
      // just do a normal initialization
      do_initializer(expr.op0(), expr.type(), false);

      // This produces a struct-expression,
      // union-expression, array-expression,
      // or an expression for a pointer or scalar.
      // We produce a compound_literal expression.
      exprt tmp(ID_compound_literal, expr.type());
      tmp.move_to_operands(expr.op0());
      expr=tmp;
      expr.set(ID_C_lvalue, true); // these are l-values
      return;
    }

    exprt new_expr;

    if(const_typecast(expr.op0(), expr.type(), new_expr) ||
       static_typecast(expr.op0(), expr.type(), new_expr, false) ||
       reinterpret_typecast(expr.op0(), expr.type(), new_expr, false))
    {
      expr=new_expr;
      add_implicit_dereference(expr);
    }
    else
    {
      error().source_location=expr.find_source_location();
      error() << "invalid explicit cast:\n"
              << "operand type: `" << to_string(expr.op0().type())
              << "'\n"
              << "casting to: `" << to_string(expr.type()) << "'"
              << eom;
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
    assert(expr.type().id()==ID_struct);

    symbol_typet symb(expr.type().get(ID_name));
    symb.add_source_location()=expr.source_location();

    exprt e=expr;
    new_temporary(e.source_location(), symb, e.operands(), expr);
  }
}

void cpp_typecheckt::typecheck_expr_this(exprt &expr)
{
  if(cpp_scopes.current_scope().class_identifier.empty())
  {
    error().source_location=expr.find_source_location();
    error() << "`this' is not allowed here" << eom;
    throw 0;
  }

  const exprt &this_expr=cpp_scopes.current_scope().this_expr;
  const source_locationt source_location=expr.find_source_location();

  assert(this_expr.is_not_nil());
  assert(this_expr.type().id()==ID_pointer);

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

  typet pointer_type=follow(expr.op0().type());

  if(pointer_type.id()!=ID_pointer)
  {
    error().source_location=expr.find_source_location();
    error() << "delete takes a pointer type operand, but got `"
            << to_string(pointer_type) << "'" << eom;
    throw 0;
  }

  // remove any const-ness of the argument
  // (which would impair the call to the destructor)
  pointer_type.subtype().remove(ID_C_constant);

  // delete expressions are always void
  expr.type()=typet(ID_empty);

  // we provide the right destructor, for the convenience
  // of later stages
  exprt new_object(ID_new_object, pointer_type.subtype());
  new_object.add_source_location()=expr.source_location();
  new_object.set(ID_C_lvalue, true);

  already_typechecked(new_object);

  auto destructor_code = cpp_destructor(expr.source_location(), new_object);

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
    error() << "error: member operator expects one operand" << eom;
    throw 0;
  }

  exprt &op0=expr.op0();
  add_implicit_dereference(op0);

  // The notation for explicit calls to destructors can be used regardless
  // of whether the type defines a destructor.  This allows you to make such
  // explicit calls without knowing if a destructor is defined for the type.
  // An explicit call to a destructor where none is defined has no effect.

  if(expr.find(ID_component_cpp_name).is_not_nil() &&
     to_cpp_name(expr.find(ID_component_cpp_name)).is_destructor() &&
     follow(op0.type()).id()!=ID_struct)
  {
    exprt tmp(ID_cpp_dummy_destructor);
    tmp.add_source_location()=expr.source_location();
    expr.swap(tmp);
    return;
  }

  // The member operator will trigger template elaboration
  elaborate_class_template(op0.type());

  const typet &followed_op0_type=follow(op0.type());

  if(followed_op0_type.id()==ID_incomplete_struct ||
     followed_op0_type.id()==ID_incomplete_union)
  {
    error().source_location=expr.find_source_location();
    error() << "error: member operator got incomplete type "
            << "on left hand side" << eom;
    throw 0;
  }

  if(followed_op0_type.id()!=ID_struct &&
     followed_op0_type.id()!=ID_union)
  {
    error().source_location=expr.find_source_location();
    error() << "error: member operator requires struct/union type "
            << "on left hand side but got `"
            << to_string(followed_op0_type) << "'" << eom;
    throw 0;
  }

  const struct_union_typet &type=
    to_struct_union_type(followed_op0_type);

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
      assert(symbol_expr.get_bool(ID_C_implicit));
      exprt tmp=symbol_expr.op0();
      symbol_expr.swap(tmp);
    }

    assert(symbol_expr.id()==ID_symbol ||
           symbol_expr.id()==ID_member ||
           symbol_expr.id()==ID_constant);

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
        error() << "error: member `"
                << lookup(symbol_expr.get(ID_identifier)).base_name
                << "' is a constructor" << eom;
        throw 0;
      }
      else
      {
        // it must be a static component
        const struct_typet::componentt pcomp=
          type.get_component(to_symbol_expr(symbol_expr).get_identifier());

        if(pcomp.is_nil())
        {
          error().source_location=expr.find_source_location();
          error() << "error: `"
                  << symbol_expr.get(ID_identifier)
                  << "' is not static member "
                  << "of class `" << to_string(type) << "'"
                  << eom;
          throw 0;
        }
      }

      expr=symbol_expr;
      return;
    }
    else if(symbol_expr.id()==ID_constant)
    {
      expr=symbol_expr;
      return;
    }

    const irep_idt component_name=symbol_expr.get(ID_component_name);

    expr.remove(ID_component_cpp_name);
    expr.set(ID_component_name, component_name);
  }

  const irep_idt &component_name=expr.get(ID_component_name);

  assert(component_name!="");

  exprt component;
  component.make_nil();

  assert(follow(expr.op0().type()).id()==ID_struct ||
         follow(expr.op0().type()).id()==ID_union);

  exprt member;

  if(get_component(expr.source_location(),
                   expr.op0(),
                   component_name,
                   member))
  {
    // because of possible anonymous members
    expr.swap(member);
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "error: member `" << component_name
            << "' of `" << to_string(type)
            << "' not found" << eom;
    throw 0;
  }

  add_implicit_dereference(expr);

  if(expr.type().id()==ID_code)
  {
    // Check if the function body has to be typechecked
    symbol_tablet::symbolst::const_iterator it=
      symbol_table.symbols.find(component_name);

    assert(it!=symbol_table.symbols.end());

    if(it->second.value.id() == ID_cpp_not_typechecked)
      symbol_table.get_writeable_ref(component_name)
        .value.set(ID_is_used, true);
  }
}

void cpp_typecheckt::typecheck_expr_ptrmember(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  assert(expr.id()==ID_ptrmember);

  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "error: ptrmember operator expects one operand" << eom;
    throw 0;
  }

  add_implicit_dereference(expr.op0());

  if(expr.op0().type().id()!=ID_pointer)
  {
    error().source_location=expr.find_source_location();
    error() << "error: ptrmember operator requires pointer type "
            << "on left hand side, but got `"
            << to_string(expr.op0().type()) << "'" << eom;
    throw 0;
  }

  exprt tmp;
  exprt &op=expr.op0();

  op.swap(tmp);

  op.id(ID_dereference);
  op.move_to_operands(tmp);
  op.add_source_location()=expr.source_location();
  typecheck_expr_dereference(op);

  expr.id(ID_member);
  typecheck_expr_member(expr, fargs);
}

void cpp_typecheckt::typecheck_cast_expr(exprt &expr)
{
  side_effect_expr_function_callt e =
    to_side_effect_expr_function_call(expr);

  if(e.arguments().size() != 1)
  {
    error().source_location=expr.find_source_location();
    error() << "cast expressions expect one operand" << eom;
    throw 0;
  }

  exprt &f_op=e.function();
  exprt &cast_op=e.arguments().front();

  add_implicit_dereference(cast_op);

  const irep_idt &id=
  f_op.get_sub().front().get(ID_identifier);

  if(f_op.get_sub().size()!=2 ||
     f_op.get_sub()[1].id()!=ID_template_args)
  {
    error().source_location=expr.find_source_location();
    error() << id << " expects template argument" << eom;
    throw 0;
  }

  irept &template_arguments=f_op.get_sub()[1].add(ID_arguments);

  if(template_arguments.get_sub().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << id << " expects one template argument" << eom;
    throw 0;
  }

  irept &template_arg=template_arguments.get_sub().front();

  if(template_arg.id() != ID_type && template_arg.id() != ID_ambiguous)
  {
    error().source_location=expr.find_source_location();
    error() << id << " expects a type as template argument" << eom;
    throw 0;
  }

  typet &type=static_cast<typet &>(
    template_arguments.get_sub().front().add(ID_type));

  typecheck_type(type);

  source_locationt source_location=expr.source_location();

  exprt new_expr;
  if(id==ID_const_cast)
  {
    if(!const_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on const_cast:\n"
              << "operand type: `" << to_string(cast_op.type())
              << "'\n"
              << "cast type: `" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_dynamic_cast)
  {
    if(!dynamic_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on dynamic_cast:\n"
              << "operand type: `" << to_string(cast_op.type())
              << "'\n"
              << "cast type: `" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_reinterpret_cast)
  {
    if(!reinterpret_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on reinterpret_cast:\n"
              << "operand type: `" << to_string(cast_op.type())
              << "'\n"
              << "cast type: `" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_static_cast)
  {
    if(!static_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on static_cast:\n"
              << "operand type: `" << to_string(cast_op.type())
              << "'\n"
              << "cast type: `" << to_string(type) << "'" << eom;
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

    if(identifier=="__sync_fetch_and_add" ||
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
      if(fargs.operands.empty())
      {
        error().source_location=source_location;
        error() << "__sync_* primitives take as least one argument"
                << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << "__sync_* primitives take a pointer as first argument"
                << eom;
        throw 0;
      }

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      code_typet t(
        {code_typet::parametert(ptr_arg.type())}, ptr_arg.type().subtype());
      t.make_ellipsis();
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_load_n")
    {
      // These are polymorphic
      // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
      // type __atomic_load_n(type *ptr, int memorder)

      if(fargs.operands.size()!=2)
      {
        error().source_location=source_location;
        error() << identifier << " expects two arguments" << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as first argument"
                << eom;
        throw 0;
      }

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      const code_typet t(
        {code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(signed_int_type())},
        ptr_arg.type().subtype());
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_store_n")
    {
      // These are polymorphic
      // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
      // void __atomic_store_n(type *ptr, type val, int memorder)

      if(fargs.operands.size()!=3)
      {
        error().source_location=source_location;
        error() << identifier << " expects three arguments" << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as first argument"
                << eom;
        throw 0;
      }

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      const code_typet t(
        {code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(ptr_arg.type().subtype()),
         code_typet::parametert(signed_int_type())},
        empty_typet());
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_exchange_n")
    {
      // These are polymorphic
      // https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
      // type __atomic_exchange_n(type *ptr, type val, int memorder)

      if(fargs.operands.size()!=3)
      {
        error().source_location=source_location;
        error() << identifier << " expects three arguments" << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as first argument"
                << eom;
        throw 0;
      }

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      const code_typet t(
        {code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(ptr_arg.type().subtype()),
         code_typet::parametert(signed_int_type())},
        ptr_arg.type().subtype());
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_load" ||
            identifier=="__atomic_store")
    {
      // void __atomic_load(type *ptr, type *ret, int memorder)
      // void __atomic_store(type *ptr, type *val, int memorder)

      if(fargs.operands.size()!=3)
      {
        error().source_location=source_location;
        error() << identifier << " expects three arguments" << eom;
        throw 0;
      }

      if(fargs.operands[0].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as first argument"
                << eom;
        throw 0;
      }

      if(fargs.operands[1].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as second argument"
                << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      const code_typet t(
        {code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(signed_int_type())},
        empty_typet());
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_exchange")
    {
      // void __atomic_exchange(type *ptr, type *val, type *ret, int memorder)

      if(fargs.operands.size()!=4)
      {
        error().source_location=source_location;
        error() << identifier << " expects four arguments" << eom;
        throw 0;
      }

      if(fargs.operands[0].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as first argument"
                << eom;
        throw 0;
      }

      if(fargs.operands[1].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as second argument"
                << eom;
        throw 0;
      }

      if(fargs.operands[2].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as third argument"
                << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      const code_typet t(
        {code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(ptr_arg.type()),
         code_typet::parametert(signed_int_type())},
        empty_typet());
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_compare_exchange_n" ||
            identifier=="__atomic_compare_exchange")
    {
      // bool __atomic_compare_exchange_n(type *ptr, type *expected, type
      // desired, bool weak, int success_memorder, int failure_memorder)
      // bool __atomic_compare_exchange(type *ptr, type *expected, type
      // *desired, bool weak, int success_memorder, int failure_memorder)

      if(fargs.operands.size()!=6)
      {
        error().source_location=source_location;
        error() << identifier << " expects six arguments" << eom;
        throw 0;
      }

      if(fargs.operands[0].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as first argument"
                << eom;
        throw 0;
      }

      if(fargs.operands[1].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as second argument"
                << eom;
        throw 0;
      }

      if(identifier=="__atomic_compare_exchange" &&
         fargs.operands[2].type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << identifier << " takes a pointer as third argument"
                << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      code_typet::parameterst parameters;
      parameters.push_back(code_typet::parametert(ptr_arg.type()));
      parameters.push_back(code_typet::parametert(ptr_arg.type()));

      if(identifier=="__atomic_compare_exchange")
        parameters.push_back(code_typet::parametert(ptr_arg.type()));
      else
        parameters.push_back(code_typet::parametert(ptr_arg.type().subtype()));

      parameters.push_back(code_typet::parametert(c_bool_type()));
      parameters.push_back(code_typet::parametert(signed_int_type()));
      parameters.push_back(code_typet::parametert(signed_int_type()));
      code_typet t(std::move(parameters), c_bool_type());
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_add_fetch" ||
            identifier=="__atomic_sub_fetch" ||
            identifier=="__atomic_and_fetch" ||
            identifier=="__atomic_xor_fetch" ||
            identifier=="__atomic_or_fetch" ||
            identifier=="__atomic_nand_fetch")
    {
      if(fargs.operands.size()!=3)
      {
        error().source_location=source_location;
        error() << "__atomic_*_fetch primitives take three arguments"
                << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << "__atomic_*_fetch primitives take pointer as first argument"
                << eom;
        throw 0;
      }

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      code_typet t(
        {code_typet::parametert(ptr_arg.type())}, ptr_arg.type().subtype());
      t.make_ellipsis();
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_fetch_add" ||
            identifier=="__atomic_fetch_sub" ||
            identifier=="__atomic_fetch_and" ||
            identifier=="__atomic_fetch_xor" ||
            identifier=="__atomic_fetch_or" ||
            identifier=="__atomic_fetch_nand")
    {
      if(fargs.operands.size()!=3)
      {
        error().source_location=source_location;
        error() << "__atomic_fetch_* primitives take three arguments"
                << eom;
        throw 0;
      }

      const exprt &ptr_arg=fargs.operands.front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        error().source_location=source_location;
        error() << "__atomic_fetch_* primitives take pointer as first argument"
                << eom;
        throw 0;
      }

      symbol_exprt result;
      result.add_source_location()=source_location;
      result.set_identifier(identifier);
      code_typet t(
        {code_typet::parametert(ptr_arg.type())}, ptr_arg.type().subtype());
      t.make_ellipsis();
      result.type()=t;
      expr.swap(result);
      return;
    }
    else if(identifier=="__atomic_test_and_set")
    {
    }
    else if(identifier=="__atomic_clear")
    {
    }
    else if(identifier=="__atomic_thread_fence")
    {
    }
    else if(identifier=="__atomic_signal_fence")
    {
    }
    else if(identifier=="__atomic_always_lock_free")
    {
    }
    else if(identifier=="__atomic_is_lock_free")
    {
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

  if(expr.get_sub().size()>=1 &&
     expr.get_sub().front().id()==ID_name)
  {
    const irep_idt &id=expr.get_sub().front().get(ID_identifier);

    if(id==ID_const_cast ||
       id==ID_dynamic_cast ||
       id==ID_reinterpret_cast ||
       id==ID_static_cast)
    {
      expr.id(ID_cast_expression);
      return;
    }
  }

  exprt symbol_expr=
    resolve(
      to_cpp_name(expr),
      cpp_typecheck_resolvet::wantt::VAR,
      fargs);

  // we want VAR
  assert(symbol_expr.id()!=ID_type);

  if(symbol_expr.id()==ID_member)
  {
    if(symbol_expr.operands().empty() ||
       symbol_expr.op0().is_nil())
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

  symbol_expr.add_source_location()=source_location;
  expr=symbol_expr;

  if(expr.id()==ID_symbol)
    typecheck_expr_function_identifier(expr);

  add_implicit_dereference(expr);
}

void cpp_typecheckt::add_implicit_dereference(exprt &expr)
{
  if(is_reference(expr.type()))
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
  // For virtual functions, it is important to check whether
  // the function name is qualified. If it is qualified, then
  // the call is not virtual.
  bool is_qualified=false;

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

  // now do the function -- this has been postponed
  typecheck_function_expr(expr.function(), cpp_typecheck_fargst(expr));

  if(expr.function().id() == ID_pod_constructor)
  {
    assert(expr.function().type().id()==ID_code);

    // This must be a POD.
    const typet &pod=to_code_type(expr.function().type()).return_type();
    assert(cpp_is_pod(pod));

    // These aren't really function calls, but either conversions or
    // initializations.
    if(expr.arguments().empty())
    {
      // create temporary object
      side_effect_exprt tmp_object_expr(
        ID_temporary_object, pod, expr.source_location());
      tmp_object_expr.set(ID_C_lvalue, true);
      tmp_object_expr.set(ID_mode, ID_cpp);
      expr.swap(tmp_object_expr);
    }
    else if(expr.arguments().size()==1)
    {
      exprt typecast("explicit-typecast");
      typecast.type()=pod;
      typecast.add_source_location()=expr.source_location();
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
  else if(expr.function().id() == ID_cast_expression)
  {
    // These are not really function calls,
    // but usually just type adjustments.
    typecheck_cast_expr(expr);
    add_implicit_dereference(expr);
    return;
  }
  else if(expr.function().id() == ID_cpp_dummy_destructor)
  {
    // these don't do anything, e.g., (char*)->~char()
    expr.set(ID_statement, ID_skip);
    expr.type()=empty_typet();
    return;
  }

  // look at type of function

  expr.function().type() = follow(expr.function().type());

  if(expr.function().type().id()==ID_pointer)
  {
    if(expr.function().type().find("to-member").is_not_nil())
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
      assert(bound.type().id()==ID_pointer);
      expr.arguments().insert(expr.arguments().begin(), bound);

      // we don't need the object any more
      expr.function().type().remove(ID_C_bound);
    }

    // do implicit dereference
    if(expr.function().id()==ID_address_of &&
      expr.function().operands().size()==1)
    {
      exprt tmp;
      tmp.swap(expr.function().op0());
      expr.function().swap(tmp);
    }
    else
    {
      assert(expr.function().type().id()==ID_pointer);
      dereference_exprt tmp(expr.function());
      tmp.add_source_location()=expr.op0().source_location();
      expr.function().swap(tmp);
    }

    if(expr.function().type().id()!=ID_code)
    {
      error().source_location=expr.op0().find_source_location();
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
        vtptr_member.move_to_operands(op0.op0());
      }
      else
      {
        vtptr_member.id(ID_ptrmember);
        exprt this_expr("cpp-this");
        vtptr_member.move_to_operands(this_expr);
      }

      // get the virtual table
      typet this_type=
        to_code_type(expr.function().type()).parameters().front().type();
      irep_idt vtable_name=
        this_type.subtype().get_string(ID_identifier) +"::@vtable_pointer";

      const struct_typet &vt_struct=
        to_struct_type(follow(this_type.subtype()));

      const struct_typet::componentt &vt_compo=
        vt_struct.get_component(vtable_name);

      assert(vt_compo.is_not_nil());

      vtptr_member.set(ID_component_name, vtable_name);

      // look for the right entry
      irep_idt vtentry_component_name =
        vt_compo.type().subtype().get_string(ID_identifier) +
        "::" + expr.function().type().get_string(ID_C_virtual_name);

      exprt vtentry_member(ID_ptrmember);
      vtentry_member.copy_to_operands(vtptr_member);
      vtentry_member.set(ID_component_name, vtentry_component_name);
      typecheck_expr(vtentry_member);

      assert(vtentry_member.type().id()==ID_pointer);

      {
        dereference_exprt tmp(vtentry_member);
        tmp.add_source_location()=expr.op0().source_location();
        vtentry_member.swap(tmp);
      }

      // Typecheck the expression as if it was not virtual
      // (add the this pointer)

      expr.type()=
        to_code_type(expr.function().type()).return_type();

      typecheck_method_application(expr);

      // Let's make the call virtual
      expr.function().swap(vtentry_member);

      typecheck_function_call_arguments(expr);
      add_implicit_dereference(expr);
      return;
    }
  }
  else if(expr.function().type().id()==ID_struct)
  {
    irept name(ID_name);
    name.set(ID_identifier, "operator()");
    name.set(ID_C_source_location, expr.source_location());

    cpp_namet cppname;
    cppname.get_sub().push_back(name);

    exprt member(ID_member);
    member.add(ID_component_cpp_name)=cppname;

    member.move_to_operands(op0);

    expr.function().swap(member);
    typecheck_side_effect_function_call(expr);

    return;
  }
  else
  {
    error().source_location=expr.function().find_source_location();
    error() << "function call expects function or function "
            << "pointer as argument, but got `"
            << to_string(expr.op0().type()) << "'" << eom;
    throw 0;
  }

  expr.type()=
    to_code_type(expr.function().type()).return_type();

  if(expr.type().id()==ID_constructor)
  {
    assert(expr.function().id() == ID_symbol);

    const code_typet::parameterst &parameters=
      to_code_type(expr.function().type()).parameters();

    assert(parameters.size()>=1);

    const typet &this_type=parameters[0].type();

    // change type from 'constructor' to object type
    expr.type()=this_type.subtype();

    // create temporary object
    side_effect_exprt tmp_object_expr(
      ID_temporary_object, this_type.subtype(), expr.source_location());
    tmp_object_expr.set(ID_C_lvalue, true);
    tmp_object_expr.set(ID_mode, ID_cpp);

    exprt member;

    exprt new_object(ID_new_object, tmp_object_expr.type());
    new_object.set(ID_C_lvalue, true);

    assert(follow(tmp_object_expr.type()).id()==ID_struct);

    get_component(expr.source_location(),
                  new_object,
                  expr.function().get(ID_identifier),
                  member);

    // special case for the initialization of parents
    if(member.get_bool(ID_C_not_accessible))
    {
      assert(member.get(ID_C_access)!="");
      tmp_object_expr.set(ID_C_not_accessible, true);
      tmp_object_expr.set(ID_C_access, member.get(ID_C_access));
    }

    // the constructor is being used, so make sure the destructor
    // will be available
    {
      // find name of destructor
      const struct_typet::componentst &components=
        to_struct_type(follow(tmp_object_expr.type())).components();

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

  assert(expr.operands().size()==2);

  if(expr.function().id()==ID_member)
    typecheck_method_application(expr);
  else
  {
    // for the object of a method call,
    // we are willing to add an "address_of"
    // for the sake of operator overloading

    const irept::subt &arguments=
      expr.function().type().find(ID_arguments).get_sub();

    if(arguments.size()>=1 &&
       arguments.front().get(ID_C_base_name)==ID_this &&
       expr.arguments().size()>=1)
    {
      const exprt &argument=
      static_cast<const exprt &>(arguments.front());

      exprt &operand=expr.op1();
      assert(argument.type().id()==ID_pointer);

      if(operand.type().id()!=ID_pointer &&
         operand.type()==argument.type().subtype())
      {
        address_of_exprt tmp(operand, pointer_type(operand.type()));
        tmp.add_source_location()=operand.source_location();
        operand=tmp;
      }
    }
  }

  assert(expr.operands().size()==2);

  typecheck_function_call_arguments(expr);

  assert(expr.operands().size()==2);

  add_implicit_dereference(expr);

  // we will deal with some 'special' functions here
  exprt tmp=do_special_functions(expr);
  if(tmp.is_not_nil())
    expr.swap(tmp);
}

/// \param type:checked arguments, type-checked function
/// \return type-adjusted function arguments
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
      assert(is_reference(parameter.type()));

      if(arg_it->id()!=ID_temporary_object)
      {
        // create a temporary for the parameter

        exprt arg(ID_already_typechecked);
        arg.copy_to_operands(*arg_it);

        exprt temporary;
        new_temporary(
          arg_it->source_location(),
          parameter.type().subtype(),
          arg,
          temporary);
        arg_it->swap(temporary);
      }
    }

    ++arg_it;
  }

  c_typecheck_baset::typecheck_function_call_arguments(expr);
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
  assert(expr.operands().size()==2);

  assert(expr.function().id()==ID_member);
  assert(expr.function().operands().size()==1);

  // turn e.f(...) into xx::f(e, ...)

  exprt member_expr;
  member_expr.swap(expr.function());

  const symbolt &symbol=lookup(member_expr.get(ID_component_name));
  symbolt &method_symbol=symbol_table.get_writeable_ref(symbol.name);
  const symbolt &tag_symbol = lookup(symbol.type.get(ID_C_member_name));

  // build the right template map
  // if this is an instantiated template class method
  if(tag_symbol.type.find(ID_C_template)!=irept())
  {
    cpp_saved_template_mapt saved_map(template_map);
    const irept &template_type = tag_symbol.type.find(ID_C_template);
    const irept &template_args = tag_symbol.type.find(ID_C_template_arguments);
    template_map.build(
      static_cast<const template_typet &>(template_type),
      static_cast<const cpp_template_args_tct &>(template_args));
    add_method_body(&method_symbol);
#ifdef DEBUG
    std::cout << "MAP for " << symbol << ":" << std::endl;
    template_map.print(std::cout);
#endif
  }
  else
    add_method_body(&method_symbol);

  // build new function expression
  exprt new_function(cpp_symbol_expr(symbol));
  new_function.add_source_location()=member_expr.source_location();
  expr.function().swap(new_function);

  if(!expr.function().type().get_bool(ID_C_is_static))
  {
    const code_typet &func_type=to_code_type(symbol.type);
    typet this_type=func_type.parameters().front().type();

    // Special case. Make it a reference.
    assert(this_type.id()==ID_pointer);
    this_type.set(ID_C_reference, true);
    this_type.set(ID_C_this, true);

    if(expr.arguments().size()==func_type.parameters().size())
    {
      // this might be set up for base-class initialisation
      if(!base_type_eq(expr.arguments().front().type(),
                      func_type.parameters().front().type(),
                      *this))
      {
        implicit_typecast(expr.arguments().front(), this_type);
        assert(is_reference(expr.arguments().front().type()));
        expr.arguments().front().type().remove(ID_C_reference);
      }
    }
    else
    {
      exprt this_arg=member_expr.op0();
      implicit_typecast(this_arg, this_type);
      assert(is_reference(this_arg.type()));
      this_arg.type().remove(ID_C_reference);
      expr.arguments().insert(expr.arguments().begin(), this_arg);
    }
  }

  if(
    symbol.value.id() == ID_cpp_not_typechecked &&
    !symbol.value.get_bool(ID_is_used))
  {
    symbol_table.get_writeable_ref(symbol.name).value.set(ID_is_used, true);
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

  typet type0=expr.op0().type();

  if(is_reference(type0))
    type0=type0.subtype();

  if(cpp_is_pod(type0))
  {
    // for structs we use the 'implicit assignment operator',
    // and therefore, it is allowed to assign to a rvalue struct.
    if(follow(type0).id()==ID_struct)
      expr.op0().set(ID_C_lvalue, true);

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
    error() << "bad assignment operator `" << statement << "'" << eom;
    throw 0;
  }

  cpp_namet cpp_name;
  cpp_name.get_sub().push_back(irept(ID_name));
  cpp_name.get_sub().front().set(ID_identifier, strop);
  cpp_name.get_sub().front().set(ID_C_source_location, expr.source_location());

  // expr.op0() is already typechecked
  exprt already_typechecked(ID_already_typechecked);
  already_typechecked.move_to_operands(expr.op0());

  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.move_to_operands(already_typechecked);

  side_effect_expr_function_callt new_expr;
  new_expr.function().swap(member);
  new_expr.arguments().push_back(expr.op1());
  new_expr.add_source_location()=expr.source_location();

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

  add_implicit_dereference(expr.op0());

  typet tmp_type=follow(expr.op0().type());

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
    error() << "bad assignment operator `"
            << expr.get_statement()
            << "'" << eom;
    throw 0;
  }

  cpp_namet cpp_name;
  cpp_name.get_sub().push_back(irept(ID_name));
  cpp_name.get_sub().front().set(ID_identifier, str_op);
  cpp_name.get_sub().front().set(ID_C_source_location, expr.source_location());

  exprt already_typechecked(ID_already_typechecked);
  already_typechecked.move_to_operands(expr.op0());

  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.move_to_operands(already_typechecked);

  side_effect_expr_function_callt new_expr;
  new_expr.function().swap(member);
  new_expr.add_source_location()=expr.source_location();

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

  exprt &op=expr.op0();
  const typet op_type=follow(op.type());

  if(op_type.id()==ID_pointer &&
     op_type.find("to-member").is_not_nil())
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
  assert(expr.id()=="pointer-to-member");
  assert(expr.operands().size() == 2);

  if(expr.op1().type().id()!=ID_pointer
     || expr.op1().type().find("to-member").is_nil())
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member expected" << eom;
    throw 0;
  }

  typet t0=expr.op0().type().id()==ID_pointer ?
  expr.op0().type().subtype():  expr.op0().type();

  typet t1((const typet&)expr.op1().type().find("to-member"));

  t0=follow(t0);
  t1=follow(t1);

  if(t0.id()!=ID_struct)
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  const struct_typet &from_struct=to_struct_type(t0);
  const struct_typet &to_struct=to_struct_type(t1);

  if(!subtype_typecast(from_struct, to_struct))
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  typecheck_expr_main(expr.op1());

  if(expr.op0().type().id()!=ID_pointer)
  {
    if(expr.op0().id()==ID_dereference)
    {
      exprt tmp=expr.op0().op0();
      expr.op0().swap(tmp);
    }
    else
    {
      assert(expr.op0().get_bool(ID_C_lvalue));
      expr.op0()=address_of_exprt(expr.op0());
    }
  }

  exprt tmp(expr.op1());
  tmp.type().set(ID_C_bound, expr.op0());
  expr.swap(tmp);
  return;
}

void cpp_typecheckt::typecheck_expr_function_identifier(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    // Check if the function body has to be typechecked
    symbol_tablet::symbolst::const_iterator it=
      symbol_table.symbols.find(expr.get(ID_identifier));

    assert(it != symbol_table.symbols.end());

    if(it->second.value.id() == ID_cpp_not_typechecked)
      symbol_table.get_writeable_ref(it->first).value.set(ID_is_used, true);
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

  assert(expr.operands().size()==1);

  irep_idt op0_id=expr.op0().id();

  if(expr.type().id()==ID_cpp_name &&
     expr.op0().operands().size()==1 &&
     (op0_id==ID_unary_plus ||
      op0_id==ID_unary_minus ||
      op0_id==ID_address_of ||
      op0_id==ID_dereference))
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
      new_binary_expr.op0().swap(expr.type());
      new_binary_expr.op1().swap(expr.op0().op0());

      if(op0_id==ID_unary_plus)
        new_binary_expr.id(ID_plus);
      else if(op0_id==ID_unary_minus)
        new_binary_expr.id(ID_minus);
      else if(op0_id==ID_address_of)
        new_binary_expr.id(ID_bitand);
      else if(op0_id==ID_dereference)
        new_binary_expr.id(ID_mult);

      new_binary_expr.add_source_location()=expr.op0().source_location();
      expr.swap(new_binary_expr);
    }
  }
}

void cpp_typecheckt::typecheck_expr_binary_arithmetic(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "operator `" << expr.id() << "' expects two operands"
            << eom;
    throw 0;
  }

  add_implicit_dereference(expr.op0());
  add_implicit_dereference(expr.op1());

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

  if(follow(expr.op0().type()).id()==ID_struct)
  {
    // TODO: check if the comma operator has been overloaded!
  }

  c_typecheck_baset::typecheck_expr_comma(expr);
}

void cpp_typecheckt::typecheck_expr_rel(binary_relation_exprt &expr)
{
  c_typecheck_baset::typecheck_expr_rel(expr);
}
