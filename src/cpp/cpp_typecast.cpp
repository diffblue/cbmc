/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <assert.h>

#include <simplify_expr_class.h>
#include <i2string.h>
#include <expr_util.h>
#include <std_types.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_typecast.h"
#include "cpp_typecheck.h"
#include "cpp_util.h"

/*******************************************************************\

Function: cpp_typecastt::cpp_typecastt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_typecastt::cpp_typecastt(cpp_typecheckt &cpp_typecheck):
  c_typecastt(cpp_typecheck),
  cpp_typecheck(cpp_typecheck)
{
}

/*******************************************************************\

Function: cpp_typecastt::check_qualifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::check_qualifiers(
  const typet &from,
  const typet &to)
{
  // check qualifiers
  c_qualifierst q_from(from), q_to(to);

  if(q_from.is_constant &&
     !q_to.is_constant)
  {
    errors.push_back("disregards const");
    return;
  }

  if(q_from.is_volatile &&
     !q_to.is_volatile)
  {
    errors.push_back("disregards volatile");
    return;
  }

  if(q_from.is_restricted &&
     !q_to.is_restricted)
  {
    errors.push_back("disregards restricted");
    return;
  }
}

/*******************************************************************\

Function: cpp_typecastt::get_bases

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::get_bases(
  const irep_idt &identifier,
  std::map<irep_idt, unsigned> &base_count)
{
  const symbolt &symbol=ns.lookup(identifier);

  if(symbol.type.id()!=ID_struct)
    return;

  const irept::subt &bases=symbol.type.find("bases").get_sub();

  forall_irep(it, bases)
  {
    assert(it->id()==ID_type);
    assert(it->get(ID_type) == ID_symbol);
    const irep_idt &base=it->find(ID_type).get(ID_identifier);
    base_count[base]++;
    get_bases(base, base_count);
  }
}

/*******************************************************************\

Function: cpp_typecastt::subtype_typecast

  Inputs:

 Outputs: false when ok, true when error

 Purpose:

\*******************************************************************/

bool cpp_typecastt::subtype_typecast(
  const typet &from,
  const typet &to,
  std::string &err)
{
  if(from==to) return false; // ok

  if(ns.follow(from)==ns.follow(to)) return false; // ok

  if(is_reference(from) && !is_reference(to))
  {
    err = "types are incompatible";
    return true; // not ok
  }

  if(!is_reference(from) && is_reference(to))
  {
    err = "types are incompatible";
    return true; // not ok
  }

  // "to" must be subtype of "from"

  irep_idt from_name;

  if(from.id()==ID_struct)
    from_name=from.get(ID_name);
  else if(from.id()==ID_symbol)
    from_name=from.get(ID_identifier);
  else
  {
    err = "types are incompatible";
    return true;
  }

  irep_idt to_name;

  if(to.id()==ID_struct)
    to_name=to.get(ID_name);
  else if(to.id()==ID_symbol)
    to_name = to.get(ID_identifier);
  else
  {
    err = "types are incompatible";
    return true;
  }

  std::map<irep_idt, unsigned> base_count;
  get_bases(from_name, base_count);

  unsigned c=base_count[to_name];

  if(c==1)
    return false; // ok
  else if(c>1)
  {
    err = "base is ambiguous";
    return true;
  }

  err ="types are incompatible";
  return true;
}


/*******************************************************************\

Function: cpp_typecastt::make_ptr_subtypecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::make_ptr_typecast(
  exprt &expr,
  const typet &src_type,
  const typet &dest_type)
{
  assert(src_type.id()==ID_pointer);
  assert(dest_type.id()==ID_pointer);

  struct_typet src_struct =
    to_struct_type(static_cast<const typet&>(ns.follow(src_type.subtype())));

  struct_typet dest_struct =
    to_struct_type(static_cast<const typet&>(ns.follow(dest_type.subtype())));

  exprt offset = subtype_offset(src_struct, dest_struct);
  if(offset.is_not_nil())
  {
    cpp_typecheck.typecheck_expr(offset);
    simplify_exprt simplify;
    simplify.simplify(offset);

    if(!offset.is_zero())
    {
      typet pvoid(ID_pointer);
      pvoid.subtype().id(ID_signedbv);
      pvoid.subtype().set(ID_width, "8");

      if(expr.type().subtype().get_bool("#constant"))
        pvoid.subtype().set("#constant",true);

      expr.make_typecast(pvoid);

      already_typechecked(expr);

      exprt tmp("+");
      tmp.move_to_operands(expr);
      tmp.move_to_operands(offset);
      cpp_typecheck.typecheck_expr(tmp);
      expr.swap(tmp);
    }
    expr.make_typecast(dest_type);
    return;
  }

  offset = subtype_offset(dest_struct, src_struct);
  if(offset.is_not_nil())
  {
    cpp_typecheck.typecheck_expr(offset);
    simplify_exprt simplify;
    simplify.simplify(offset);

    if(!offset.is_zero())
    {
      typet pvoid(ID_pointer);
      pvoid.subtype().id(ID_signedbv);
      pvoid.subtype().set(ID_width, "8");

      if(expr.type().subtype().get_bool("#constant"))
        pvoid.subtype().set("#constant", true);

      expr.make_typecast(pvoid);

      already_typechecked(expr);

      exprt tmp("-");
      tmp.move_to_operands(expr);
      tmp.move_to_operands(offset);
      cpp_typecheck.typecheck_expr(tmp);
      expr.swap(tmp);
    }

    expr.make_typecast(dest_type);
    return;
  }

  errors.push_back("conversion not permitted");
  return;

}

/*******************************************************************\

Function: cpp_typecastt::implicit_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::implicit_typecast(
  exprt &expr,
  const typet &type)
{
  c_typecastt::implicit_typecast(expr, type);
}

/*******************************************************************\

Function: cpp_typecastt::implicit_typecast_followed

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::implicit_typecast_followed(
  exprt &expr,
  const typet &src_type,
  const typet &dest_type)
{
  if(is_reference(dest_type))
  {
    if(is_reference(src_type))
    {
      std::string err;
      if(subtype_typecast(src_type.subtype(), dest_type.subtype(),err))
      {
        errors.push_back(err);
        return;
      }

      check_qualifiers(src_type.subtype(), dest_type.subtype());

      if(src_type==dest_type)
        expr.type()=dest_type; // because of qualifiers
      else
        make_ptr_typecast(expr,src_type, dest_type);
    }
    else // expr is not a reference
    {
      if(expr.get_bool(ID_C_lvalue))
      {
        std::string err;
        if(subtype_typecast(src_type, dest_type.subtype(),err))
        {
          errors.push_back(err);
          return;
        }

        check_qualifiers(src_type, dest_type.subtype());

        typet reference=reference_typet();
        reference.subtype() = expr.type();

        exprt tmp(ID_address_of, reference);
        tmp.set(ID_C_lvalue, true);
        tmp.location() = expr.location();
        tmp.move_to_operands(expr);
        expr.swap(tmp);

        // redo, but this time expr is a reference
        implicit_typecast_followed(expr,reference, dest_type);
        return;
      }
      else
      {
        // need temporary object
        if(dest_type.subtype().get_bool(ID_C_constant))
        {
          if(integral_conversion(src_type, dest_type.subtype()))
          {
            std::string err;
            if(subtype_typecast(src_type, dest_type.subtype(),err))
            {
              errors.push_back(err);
              return;
            }
          }
          else
          {
            // do an integral conversion first
            if(src_type !=dest_type.subtype())
            {
              expr.make_typecast(dest_type.subtype());
              // redo but this time src_type = dest_type.subtype()
              implicit_typecast_followed(expr, expr.type(), dest_type);
              return;
            }
          }

          check_qualifiers(src_type.subtype(), dest_type.subtype());

          // create temporary object
          exprt tmp_object_expr=exprt(ID_sideeffect, expr.type());

          tmp_object_expr.type().set(ID_C_constant, false);
          tmp_object_expr.set(ID_statement, ID_temporary_object);
          tmp_object_expr.set(ID_C_lvalue, true);
          tmp_object_expr.location()=expr.location();


          if(cpp_typecheck.cpp_is_pod(src_type))
            tmp_object_expr.move_to_operands(expr);
          else
          {

            exprt new_object("new_object", tmp_object_expr.type());
            new_object.set(ID_C_lvalue, true);
            new_object.location()=tmp_object_expr.location();

            already_typechecked(new_object);

            exprt reference(ID_address_of, reference_typet());
            reference.location() = expr.location();
            reference.type().subtype() = expr.type();
            reference.copy_to_operands(expr);

            already_typechecked(reference);

            exprt::operandst ops;
            ops.push_back(reference);

            // Note that implicit_typecast is called again but
            // this time both dest and sources are references.
            codet new_code =
              cpp_typecheck.cpp_constructor(expr.location(),new_object, ops);
            assert(new_code.is_not_nil());
            tmp_object_expr.add("initializer") = new_code;
          }

          typet new_src_type = follow_with_qualifiers(tmp_object_expr.type());

          // redo but this time expr is an lvalue.
          implicit_typecast_followed(tmp_object_expr,new_src_type,dest_type);
          expr.swap(tmp_object_expr);
          return;
        }
        else
        {
          errors.push_back("converting non-lvalue to non-const reference");
          return;
        }
      }
    }
    return; // ok
  }
  else if(dest_type.id()==ID_pointer)
  {
    assert(!is_reference(dest_type));

    if(src_type.id()==ID_pointer || src_type.id()==ID_array)
    {
      if(is_reference(src_type))
      {
          errors.push_back("conversion not permitted");
          return;
      }
      else if(dest_type.subtype().id()==ID_empty)
      {
        // to and from void * is ok, unless it's a function pointer
      }
      else if(src_type.subtype().id()==ID_empty)
      {
        if(dest_type.subtype().id()==ID_code)
        {
          errors.push_back("converting void pointer to function pointer");
          return;
        }
      }
      else if(dest_type.find("to-member").is_not_nil())
      {
        if(dest_type != src_type)
        {
          errors.push_back("pointer-to-member typecast error");
          return;
        }
      }
      else if(src_type.find("to-member").is_not_nil())
      {
          errors.push_back("converting pointer-to-member to pointer");
          return;
      }
      else
      {
        std::string err;
        if(integral_conversion(src_type.subtype(), dest_type.subtype())
          && subtype_typecast(src_type.subtype(), dest_type.subtype(),err))
        {
          errors.push_back(err);
          return;
        }
      }

      // check qualifiers in either case
      check_qualifiers(src_type.subtype(), dest_type.subtype());

      if(src_type==dest_type)
        expr.type()=dest_type; // because of qualifiers
      else if(dest_type.subtype().id() == ID_symbol
         && ns.follow(dest_type.subtype()).id() == ID_struct)
        make_ptr_typecast(expr,src_type,dest_type);
      else
        do_typecast(expr, dest_type);
      return; // ok
    }
  }
  else if(dest_type.id()==ID_struct)
  {
    if(is_reference(src_type))
    {
      exprt dereference(ID_dereference, expr.type().subtype());
      dereference.set(ID_C_implicit, true);
      dereference.location() = expr.location();
      dereference.copy_to_operands(expr);
      typet new_src_type = follow_with_qualifiers(dereference.type());

      // redo, but this time expr is not a reference
      implicit_typecast_followed(dereference, new_src_type, dest_type);
      expr.swap(dereference);
      return;
    }

    // Derived to base conversion
    std::string err;
    if(!subtype_typecast(src_type, dest_type,err))
    {

      c_qualifierst src_qualifiers(src_type);
      typet src_sym_type(ID_symbol);
      src_sym_type.set(ID_identifier, src_type.get(ID_name));
      src_qualifiers.write(src_sym_type);

      c_qualifierst dest_qualifiers(dest_type);
      typet dest_sym_type(ID_symbol);
      dest_sym_type.set(ID_identifier, dest_type.get(ID_name));
      dest_qualifiers.write(dest_sym_type);

      if(src_type == dest_type)
      {
        expr.type()=dest_sym_type; // because of qualifiers
      }
      else
      {
        typet pointer_src(ID_pointer);
        pointer_src.subtype() = src_sym_type;
        exprt pointer_to_expr(ID_address_of, pointer_src);
        pointer_to_expr.copy_to_operands(expr);

        typet pointer_dest(ID_pointer);
        pointer_dest.subtype() = dest_sym_type;
        make_ptr_typecast(pointer_to_expr, pointer_to_expr.type(), pointer_dest);
        exprt dereference(ID_dereference, dest_sym_type);
        dereference.move_to_operands(pointer_to_expr);
        dereference.set(ID_C_lvalue, expr.get_bool(ID_C_lvalue));
        expr.swap(dereference);
      }
      return;
    }
    else
    {
      // constructor conversion

      const struct_typet &struct_type=
      to_struct_type(dest_type);

      const struct_typet::componentst &components=
      struct_type.components();

      // let's look for a suitable constructor
      int count = 0;
      exprt arg1;

      forall_expr(it, components)
      {
        const typet &type=it->type();

        if(it->get_bool("from_base") ||
           type.id()!=ID_code ||
           type.find(ID_return_type).id()!=ID_constructor)
          continue;

        // TODO: ellipsis

        const irept &arguments = type.find(ID_arguments);

        if(arguments.get_sub().size() != 2)
          continue;

        exprt curr_arg1 = static_cast<const exprt&> (arguments.get_sub()[1]);

        typet arg1_type = curr_arg1.type();

        if(is_reference(arg1_type))
        {
          typet tmp=arg1_type.subtype();
          arg1_type.swap(tmp);
        }

        std::string err;
        if(subtype_typecast(src_type, cpp_typecheck.follow(arg1_type), err))
          continue;
        count++;

        arg1 = curr_arg1;
      }

      if(count == 0)
      {
        errors.push_back("type are incompatible");
        return;
      }
      else if(count > 1)
      {
        errors.push_back("constructor-conversion is ambiguous");
        return;
      }

      exprt tmp_expr(expr);
      typet new_dest_type = follow_with_qualifiers(arg1.type());
      implicit_typecast_followed(tmp_expr,src_type, new_dest_type);
      already_typechecked(tmp_expr);

      c_qualifierst dest_qualifiers(dest_type);
      typet dest_sym_type(ID_symbol);
      dest_sym_type.set(ID_identifier, dest_type.get(ID_name));
      dest_qualifiers.write(dest_sym_type);

      // create temporary object
      exprt tmp_object_expr=exprt(ID_sideeffect, dest_sym_type);
      tmp_object_expr.set(ID_statement, ID_temporary_object);
      tmp_object_expr.location()=expr.location();
      tmp_object_expr.set(ID_C_lvalue, true);

      assert(!cpp_typecheck.cpp_is_pod(dest_type));

      exprt new_object("new_object",tmp_object_expr.type());
      new_object.location() = tmp_object_expr.location();
      new_object.set(ID_C_lvalue, true);

      already_typechecked(new_object);

      exprt::operandst ops;
      ops.push_back(tmp_expr);

      codet new_code =
      cpp_typecheck.cpp_constructor(expr.location(),new_object, ops);
      assert(new_code.is_not_nil());
      tmp_object_expr.add("initializer") = new_code;

      expr.swap(tmp_object_expr);
      return;
    }
  }

  // C++, in contrast to C, does not allow conversions between
  // diferent enum types

  if(src_type.id()=="c_enum" &&
     dest_type.id()=="c_enum" &&
     src_type!=dest_type)
  {
    errors.push_back("conversion between enum-types not permitted");
    return;
  }
  else if(src_type.id()==ID_pointer)
  {
    if(dest_type.id()!=ID_bool)
    {
      errors.push_back("conversion not permitted");
      return;
    }
  }

  c_typecastt::implicit_typecast_followed(expr, src_type, dest_type);
}

/*******************************************************************\

Function: cpp_typecastt::integral_conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_typecastt::integral_conversion(
  const typet &src_type,
  const typet &dest_type)
{

  if(src_type.id() != ID_signedbv
    && src_type.id() != ID_unsignedbv
    && src_type.id() != ID_c_enum
    && src_type.id() != ID_integer
    && src_type.id() != ID_char
    && src_type.id() != ID_bool)
    return true;  // not ok

  if(dest_type.id() != ID_signedbv
    && dest_type.id() != ID_unsignedbv
    && dest_type.id() != ID_c_enum
    && dest_type.id() != ID_integer
    && dest_type.id() != ID_char
    && dest_type.id() != ID_bool)
    return true;  //not ok

  return false; // ok

}

/*******************************************************************\

Function: cpp_typecastt::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::implicit_typecast_arithmetic(exprt &expr)
{
  //c_typecastt::implicit_typecast_arithmetic(expr);
}

/*******************************************************************\

Function: cpp_typecastt::implicit_typecast_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecastt::implicit_typecast_arithmetic(
  exprt &expr1,
  exprt &expr2)
{
  c_typecastt::implicit_typecast_arithmetic(expr1, expr2);
}
