/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/arith_tools.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <util/c_types.h>

#include "cpp_util.h"

/// \param parent_base_name: base name of typechecked parent
/// \param block: non-typechecked block
/// \return generate code to copy the parent
static void copy_parent(
  const source_locationt &source_location,
  const irep_idt &parent_base_name,
  const irep_idt &arg_name,
  exprt &block)
{
  block.operands().push_back(codet());

  codet &code=to_code(block.operands().back());
  code.add_source_location()=source_location;

  code.set_statement(ID_assign);
  code.operands().push_back(exprt(ID_dereference));

  code.op0().operands().push_back(exprt("explicit-typecast"));

  exprt &op0=code.op0().op0();

  op0.operands().push_back(exprt("cpp-this"));
  op0.type()=
    pointer_type(cpp_namet(parent_base_name, source_location).as_type());
  op0.add_source_location()=source_location;

  code.operands().push_back(exprt("explicit-typecast"));
  exprt &op1=code.op1();

  op1.type() =
    pointer_type(cpp_namet(parent_base_name, source_location).as_type());
  op1.type().set(ID_C_reference, true);
  op1.type().subtype().set(ID_C_constant, true);

  op1.operands().push_back(exprt(ID_cpp_name));
  op1.op0().get_sub().push_back(irept(ID_name));
  op1.op0().get_sub().back().set(ID_identifier, arg_name);
  op1.op0().get_sub().back().set(ID_C_source_location, source_location);
  op1.add_source_location()=source_location;
}

/// \param member_base_name: name of a member
/// \param block: non-typechecked block
/// \return generate code to copy the member
static void copy_member(
  const source_locationt &source_location,
  const irep_idt &member_base_name,
  const irep_idt &arg_name,
  exprt &block)
{
  block.operands().push_back(exprt(ID_code));
  exprt &code=block.operands().back();

  code.set(ID_statement, ID_expression);
  code.add(ID_type)=typet(ID_code);
  code.operands().push_back(exprt(ID_side_effect));
  code.op0().set(ID_statement, ID_assign);
  code.op0().operands().push_back(exprt(ID_cpp_name));
  code.add_source_location()=source_location;

  exprt &op0=code.op0().op0();
  op0.add_source_location()=source_location;

  op0.get_sub().push_back(irept(ID_name));
  op0.get_sub().back().set(ID_identifier, member_base_name);
  op0.get_sub().back().set(ID_C_source_location, source_location);

  code.op0().operands().push_back(exprt(ID_member));

  exprt &op1=code.op0().op1();

  op1.add(ID_component_cpp_name).id(ID_cpp_name);
  op1.add(ID_component_cpp_name).get_sub().push_back(irept(ID_name));
  op1.add(ID_component_cpp_name).get_sub().back().set(
    ID_identifier, member_base_name);
  op1.add(ID_component_cpp_name).get_sub().back().set(
    ID_C_source_location, source_location);

  op1.operands().push_back(exprt(ID_cpp_name));
  op1.op0().get_sub().push_back(irept(ID_name));
  op1.op0().get_sub().back().set(ID_identifier, arg_name);
  op1.op0().get_sub().back().set(ID_C_source_location, source_location);
  op1.add_source_location()=source_location;
}

/// \param member_base_name: name of array member
/// \param index: index to copy
/// \param block: non-typechecked block
/// \return generate code to copy the member
static void copy_array(
  const source_locationt &source_location,
  const irep_idt &member_base_name,
  mp_integer i,
  const irep_idt &arg_name,
  exprt &block)
{
  // Build the index expression
  exprt constant=from_integer(i, index_type());

  block.operands().push_back(exprt(ID_code));
  exprt &code=block.operands().back();
  code.add_source_location()=source_location;

  code.set(ID_statement, ID_expression);
  code.add(ID_type)=typet(ID_code);
  code.operands().push_back(exprt(ID_side_effect));
  code.op0().set(ID_statement, ID_assign);
  code.op0().operands().push_back(exprt(ID_index));
  exprt &op0=code.op0().op0();
  op0.operands().push_back(exprt(ID_cpp_name));
  op0.add_source_location()=source_location;

  op0.op0().get_sub().push_back(irept(ID_name));
  op0.op0().get_sub().back().set(ID_identifier, member_base_name);
  op0.op0().get_sub().back().set(ID_C_source_location, source_location);
  op0.copy_to_operands(constant);

  code.op0().operands().push_back(exprt(ID_index));

  exprt &op1=code.op0().op1();
  op1.operands().push_back(exprt(ID_member));
  op1.op0().add(ID_component_cpp_name).id(ID_cpp_name);
  op1.op0().add(ID_component_cpp_name).get_sub().push_back(irept(ID_name));
  op1.op0().add(ID_component_cpp_name).get_sub().back().set(
    ID_identifier, member_base_name);
  op1.op0().add(ID_component_cpp_name).get_sub().back().set(
    ID_C_source_location, source_location);

  op1.op0().operands().push_back(exprt(ID_cpp_name));
  op1.op0().op0().get_sub().push_back(irept(ID_name));
  op1.op0().op0().get_sub().back().set(ID_identifier, arg_name);
  op1.op0().op0().get_sub().back().set(ID_C_source_location, source_location);
  op1.copy_to_operands(constant);

  op1.add_source_location()=source_location;
}

/// Generate code for implicit default constructors
void cpp_typecheckt::default_ctor(
  const source_locationt &source_location,
  const irep_idt &base_name,
  cpp_declarationt &ctor) const
{
  cpp_declaratort decl;
  decl.name() = cpp_namet(base_name, source_location);
  decl.type()=typet(ID_function_type);
  decl.type().subtype().make_nil();
  decl.add_source_location()=source_location;

  decl.value().id(ID_code);
  decl.value().type()=typet(ID_code);
  decl.value().set(ID_statement, ID_block);
  decl.add(ID_cv).make_nil();
  decl.add(ID_throw_decl).make_nil();

  ctor.type().id(ID_constructor);
  ctor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  ctor.move_to_operands(decl);
  ctor.add_source_location()=source_location;
}

/// Generate code for implicit default copy constructor
void cpp_typecheckt::default_cpctor(
  const symbolt &symbol,
  cpp_declarationt &cpctor) const
{
  source_locationt source_location=symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)+
    "::"+id2string(symbol.base_name)+
    "(const "+id2string(symbol.base_name)+" &)");

  // Produce default constructor first
  default_ctor(source_location, symbol.base_name, cpctor);
  cpp_declaratort &decl0=cpctor.declarators()[0];

  std::string param_identifier("ref");

  // Compound name
  const cpp_namet cppcomp(symbol.base_name, source_location);

  // Parameter name
  const cpp_namet cpp_parameter(param_identifier, source_location);

  // Parameter declarator
  cpp_declaratort parameter_tor;
  parameter_tor.add(ID_value).make_nil();
  parameter_tor.set(ID_name, cpp_parameter);
  parameter_tor.type()=reference_type(nil_typet());
  parameter_tor.add_source_location()=source_location;

  // Parameter declaration
  cpp_declarationt parameter_decl;
  parameter_decl.set(ID_type, ID_merged_type);
  auto &sub = to_type_with_subtypes(parameter_decl.type()).subtypes();
  sub.push_back(cppcomp.as_type());
  irept constnd(ID_const);
  sub.push_back(static_cast<const typet &>(constnd));
  parameter_decl.move_to_operands(parameter_tor);
  parameter_decl.add_source_location()=source_location;

  // Add parameter to function type
  decl0.add(ID_type).add(ID_parameters).get_sub().push_back(parameter_decl);
  decl0.add_source_location()=source_location;

  irept &initializers=decl0.add(ID_member_initializers);
  initializers.id(ID_member_initializers);

  cpp_declaratort &declarator=static_cast<cpp_declaratort &>(cpctor.op0());
  exprt &block=declarator.value();

  // First, we need to call the parent copy constructors
  const irept &bases=symbol.type.find(ID_bases);
  forall_irep(parent_it, bases.get_sub())
  {
    assert(parent_it->id()==ID_base);
    assert(parent_it->get(ID_type) == ID_symbol_type);

    const symbolt &parsymb=
      lookup(parent_it->find(ID_type).get(ID_identifier));

    if(cpp_is_pod(parsymb.type))
      copy_parent(source_location, parsymb.base_name, param_identifier, block);
    else
    {
      irep_idt ctor_name=parsymb.base_name;

      // Call the parent default copy constructor
      const cpp_namet cppname(ctor_name, source_location);

      codet mem_init(ID_member_initializer);
      mem_init.add_source_location()=source_location;
      mem_init.set(ID_member, cppname);
      mem_init.copy_to_operands(cpp_parameter.as_expr());
      initializers.move_to_sub(mem_init);
    }
  }

  // Then, we add the member initializers
  const struct_typet::componentst &components=
    to_struct_type(symbol.type).components();

  for(const auto &mem_c : components)
  {
    // Take care of virtual tables
    if(mem_c.get_bool(ID_is_vtptr))
    {
      const cpp_namet cppname(mem_c.get_base_name(), source_location);

      const symbolt &virtual_table_symbol_type =
        lookup(mem_c.type().subtype().get(ID_identifier));

      const symbolt &virtual_table_symbol_var = lookup(
        id2string(virtual_table_symbol_type.name) + "@" +
        id2string(symbol.name));

      exprt var=virtual_table_symbol_var.symbol_expr();
      address_of_exprt address(var);
      assert(address.type() == mem_c.type());

      already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, mem_c.get_name());
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_assignt assign(ptrmember, address);
      initializers.move_to_sub(assign);
      continue;
    }

    if(
      mem_c.get_bool(ID_from_base) || mem_c.get_bool(ID_is_type) ||
      mem_c.get_bool(ID_is_static) || mem_c.type().id() == ID_code)
    {
      continue;
    }

    const irep_idt &mem_name = mem_c.get_base_name();

    const cpp_namet cppname(mem_name, source_location);

    codet mem_init(ID_member_initializer);
    mem_init.set(ID_member, cppname);
    mem_init.add_source_location()=source_location;

    exprt memberexpr(ID_member);
    memberexpr.set(ID_component_cpp_name, cppname);
    memberexpr.copy_to_operands(cpp_parameter.as_expr());
    memberexpr.add_source_location()=source_location;

    if(mem_c.type().id() == ID_array)
      memberexpr.set(ID_C_array_ini, true);

    mem_init.move_to_operands(memberexpr);
    initializers.move_to_sub(mem_init);
  }
}

/// Generate declaration of the implicit default assignment operator
void cpp_typecheckt::default_assignop(
  const symbolt &symbol,
  cpp_declarationt &cpctor)
{
  source_locationt source_location=symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)
    + "& "+
    id2string(symbol.base_name)+
    "::operator=( const "+id2string(symbol.base_name)+"&)");

  std::string arg_name("ref");

  cpctor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  cpctor.type().id(ID_symbol_type);
  cpctor.type().add(ID_identifier).id(symbol.name);
  cpctor.operands().push_back(exprt(ID_cpp_declarator));
  cpctor.add_source_location()=source_location;

  cpp_declaratort &declarator=(cpp_declaratort&) cpctor.op0();
  declarator.add_source_location()=source_location;

  cpp_namet &declarator_name=declarator.name();
  typet &declarator_type=declarator.type();

  declarator_type.add_source_location()=source_location;

  declarator_name.id(ID_cpp_name);
  declarator_name.get_sub().push_back(irept(ID_operator));
  declarator_name.get_sub().push_back(irept("="));

  declarator_type.id(ID_function_type);
  declarator_type.subtype()=reference_type(nil_typet());
  declarator_type.subtype().add(ID_C_qualifier).make_nil();

  exprt &args=static_cast<exprt&>(declarator.type().add(ID_parameters));
  args.add_source_location()=source_location;

  args.get_sub().push_back(irept(ID_cpp_declaration));

  cpp_declarationt &args_decl=
    static_cast<cpp_declarationt&>(args.get_sub().back());

  auto &args_decl_type_sub = to_type_with_subtypes(args_decl.type()).subtypes();

  args_decl.type().id(ID_merged_type);
  args_decl_type_sub.push_back(
    cpp_namet(symbol.base_name, source_location).as_type());

  args_decl_type_sub.push_back(typet(ID_const));
  args_decl.operands().push_back(exprt(ID_cpp_declarator));
  args_decl.add_source_location()=source_location;

  cpp_declaratort &args_decl_declor=
    static_cast<cpp_declaratort&>(args_decl.operands().back());

  args_decl_declor.name() = cpp_namet(arg_name, source_location);
  args_decl_declor.add_source_location()=source_location;

  args_decl_declor.type()=pointer_type(typet(ID_nil));
  args_decl_declor.type().set(ID_C_reference, true);
  args_decl_declor.value().make_nil();
}

/// Generate code for the implicit default assignment operator
void cpp_typecheckt::default_assignop_value(
  const symbolt &symbol,
  cpp_declaratort &declarator)
{
  // save source location
  source_locationt source_location=declarator.source_location();
  declarator.make_nil();

  declarator.value().add_source_location()=source_location;
  declarator.value().id(ID_code);
  declarator.value().set(ID_statement, ID_block);
  declarator.value().type() = code_typet({}, empty_typet());

  exprt &block=declarator.value();

  std::string arg_name("ref");

  // First, we copy the parents
  const irept &bases=symbol.type.find(ID_bases);

  forall_irep(parent_it, bases.get_sub())
  {
    assert(parent_it->id()==ID_base);
    assert(parent_it->get(ID_type) == ID_symbol_type);

    const symbolt &symb=
      lookup(parent_it->find(ID_type).get(ID_identifier));

    copy_parent(source_location, symb.base_name, arg_name, block);
  }

  // Then, we copy the members
  for(const auto &c : to_struct_type(symbol.type).components())
  {
    if(
      c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
      c.get_bool(ID_is_static) || c.get_bool(ID_is_vtptr) ||
      c.get(ID_type) == ID_code)
    {
      continue;
    }

    const irep_idt &mem_name = c.get_base_name();

    if(c.get(ID_type) == ID_array)
    {
      const exprt &size_expr = to_array_type((typet &)c.find(ID_type)).size();

      if(size_expr.id()==ID_infinity)
      {
        // error().source_location=object);
        // err << "cannot copy array of infinite size\n";
        // throw 0;
        continue;
      }

      mp_integer size;
      bool to_int=to_integer(size_expr, size);
      CHECK_RETURN(!to_int);
      CHECK_RETURN(size>=0);

      exprt::operandst empty_operands;
      for(mp_integer i=0; i < size; ++i)
        copy_array(source_location, mem_name, i, arg_name, block);
    }
    else
      copy_member(source_location, mem_name, arg_name, block);
  }

  // Finally we add the return statement
  block.operands().push_back(exprt(ID_code));
  exprt &ret_code=declarator.value().operands().back();
  ret_code.operands().push_back(exprt(ID_dereference));
  ret_code.op0().operands().push_back(exprt("cpp-this"));
  ret_code.set(ID_statement, ID_return);
  ret_code.type() = code_typet({}, empty_typet());
}

/// Check a constructor initialization-list. An initializer has to be a data
/// member declared in this class or a direct-parent constructor.
/// \param bases: the parents of the class
/// \param components: the components of the class
/// \param initializers: the constructor initializers
/// \return If an invalid initializer is found, then the method outputs an error
///   message and throws a 0 exception.
void cpp_typecheckt::check_member_initializers(
  const irept &bases,
  const struct_typet::componentst &components,
  const irept &initializers)
{
  assert(initializers.id()==ID_member_initializers);

  forall_irep(init_it, initializers.get_sub())
  {
    const irept &initializer=*init_it;
    assert(initializer.is_not_nil());

    const cpp_namet &member_name=
      to_cpp_name(initializer.find(ID_member));

    bool has_template_args=member_name.has_template_args();

    if(has_template_args)
    {
      // it has to be a parent constructor
      typet member_type=(typet&) initializer.find(ID_member);
      typecheck_type(member_type);

      // check for a direct parent
      bool ok=false;
      forall_irep(parent_it, bases.get_sub())
      {
        assert(parent_it->get(ID_type) == ID_symbol_type);

        if(member_type.get(ID_identifier)
          ==parent_it->find(ID_type).get(ID_identifier))
        {
          ok=true;
          break;
        }
      }

      if(!ok)
      {
        error().source_location=member_name.source_location();
        error() << "invalid initializer `" << member_name.to_string()
                << "'" << eom;
        throw 0;
      }
      return;
    }

    irep_idt base_name=member_name.get_base_name();
    bool ok=false;

    for(const auto &c : components)
    {
      if(c.get_base_name() != base_name)
        continue;

      // Data member
      if(
        !c.get_bool(ID_from_base) && !c.get_bool(ID_is_static) &&
        c.get(ID_type) != ID_code)
      {
        ok=true;
        break;
      }

      // Maybe it is a parent constructor?
      if(c.get_bool(ID_is_type))
      {
        typet type = static_cast<const typet &>(c.find(ID_type));
        if(type.id() != ID_symbol_type)
          continue;

        const symbolt &symb=lookup(type.get(ID_identifier));
        if(symb.type.id()!=ID_struct)
          break;

        // check for a direct parent
        forall_irep(parent_it, bases.get_sub())
        {
          assert(parent_it->get(ID_type) == ID_symbol_type);
          if(symb.name==parent_it->find(ID_type).get(ID_identifier))
          {
            ok=true;
            break;
          }
        }
        continue;
      }

      // Parent constructor
      if(
        c.get_bool(ID_from_base) && !c.get_bool(ID_is_type) &&
        !c.get_bool(ID_is_static) && c.type().id() == ID_code &&
        to_code_type(c.type()).return_type().id() == ID_constructor)
      {
        typet member_type=(typet&) initializer.find(ID_member);
        typecheck_type(member_type);

        // check for a direct parent
        forall_irep(parent_it, bases.get_sub())
        {
          assert(parent_it->get(ID_type) == ID_symbol_type);

          if(member_type.get(ID_identifier)==
             parent_it->find(ID_type).get(ID_identifier))
          {
            ok=true;
            break;
          }
        }
        break;
      }
    }

    if(!ok)
    {
      error().source_location=member_name.source_location();
      error() << "invalid initializer `" << base_name << "'" << eom;
      throw 0;
    }
  }
}

/// Build the full initialization list of the constructor. First, all the
/// direct-parent constructors are called. Second, all the non-pod data members
/// are initialized.
///
///    Note: The initialization order follows the declaration order.
/// \param struct_union_type: the class/struct/union
/// \param initializers: the constructor initializers
/// \return initializers is updated.
void cpp_typecheckt::full_member_initialization(
  const struct_union_typet &struct_union_type,
  irept &initializers)
{
  const struct_union_typet::componentst &components=
    struct_union_type.components();

  assert(initializers.id()==ID_member_initializers);

  irept final_initializers(ID_member_initializers);

  if(struct_union_type.id()==ID_struct)
  {
    // First, if we are the most-derived object, then
    // we need to construct the virtual bases
    std::list<irep_idt> vbases;
    get_virtual_bases(to_struct_type(struct_union_type), vbases);

    if(!vbases.empty())
    {
      // TODO(tautschnig): this code doesn't seem to make much sense as the
      // ifthenelse only gets to have two operands (instead of three)
      codet cond(ID_ifthenelse);

      cond.copy_to_operands(cpp_namet("@most_derived").as_expr());

      code_blockt block;

      while(!vbases.empty())
      {
        const symbolt &symb=lookup(vbases.front());
        if(!cpp_is_pod(symb.type))
        {
          // default initializer
          const cpp_namet cppname(symb.base_name);

          codet mem_init(ID_member_initializer);
          mem_init.set(ID_member, cppname);
          block.move_to_sub(mem_init);
        }
        vbases.pop_front();
      }
      cond.move_to_operands(block);
      final_initializers.move_to_sub(cond);
    }

    const irept &bases=struct_union_type.find(ID_bases);

    // Subsequently, we need to call the non-POD parent constructors
    forall_irep(parent_it, bases.get_sub())
    {
      assert(parent_it->id()==ID_base);
      assert(parent_it->get(ID_type) == ID_symbol_type);

      const symbolt &ctorsymb=
        lookup(parent_it->find(ID_type).get(ID_identifier));

      if(cpp_is_pod(ctorsymb.type))
        continue;

      irep_idt ctor_name=ctorsymb.base_name;

      // Check if the initialization list of the constructor
      // explicitly calls the parent constructor.
      bool found=false;

      forall_irep(m_it, initializers.get_sub())
      {
        irept initializer=*m_it;

        const cpp_namet &member_name=
          to_cpp_name(initializer.find(ID_member));

        bool has_template_args=member_name.has_template_args();

        if(!has_template_args)
        {
          irep_idt base_name=member_name.get_base_name();

          // check if the initializer is a data
          bool is_data=false;

          for(const auto &c : components)
          {
            if(
              c.get_base_name() == base_name && c.get(ID_type) != ID_code &&
              !c.get_bool(ID_is_type))
            {
              is_data=true;
              break;
            }
          }

          if(is_data)
            continue;
        }

        typet member_type=
          static_cast<const typet&>(initializer.find(ID_member));

        typecheck_type(member_type);

        if(member_type.id() != ID_symbol_type)
          break;

        if(parent_it->find(ID_type).get(ID_identifier)==
           member_type.get(ID_identifier))
        {
          final_initializers.move_to_sub(initializer);
          found=true;
          break;
        }
      }

      // Call the parent default constructor
      if(!found)
      {
        const cpp_namet cppname(ctor_name);

        codet mem_init(ID_member_initializer);
        mem_init.set(ID_member, cppname);
        final_initializers.move_to_sub(mem_init);
      }

      if(parent_it->get_bool(ID_virtual))
      {
        // TODO(tautschnig): this code doesn't seem to make much sense as the
        // ifthenelse only gets to have two operands (instead of three)
        codet cond(ID_ifthenelse);

        cond.copy_to_operands(cpp_namet("@most_derived").as_expr());

        {
          codet tmp(ID_member_initializer);
          tmp.swap(final_initializers.get_sub().back());
          cond.move_to_operands(tmp);
          final_initializers.get_sub().back().swap(cond);
        }
      }
    }
  }

  // Then, we add the member initializers
  for(const auto &c : components)
  {
    // Take care of virtual tables
    if(c.get_bool(ID_is_vtptr))
    {
      const cpp_namet cppname(c.get_base_name(), c.source_location());

      const symbolt &virtual_table_symbol_type =
        lookup(c.type().subtype().get(ID_identifier));

      const symbolt &virtual_table_symbol_var  =
        lookup(id2string(virtual_table_symbol_type.name) + "@" +
            id2string(struct_union_type.get(ID_name)));

      exprt var=virtual_table_symbol_var.symbol_expr();
      address_of_exprt address(var);
      assert(address.type() == c.type());

      already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, c.get_name());
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_assignt assign(ptrmember, address);
      final_initializers.move_to_sub(assign);
      continue;
    }

    if(
      c.get_bool(ID_from_base) || c.type().id() == ID_code ||
      c.get_bool(ID_is_type) || c.get_bool(ID_is_static))
    {
      continue;
    }

    const irep_idt &mem_name = c.get_base_name();

    // Check if the initialization list of the constructor
    // explicitly initializes the data member
    bool found=false;
    Forall_irep(m_it, initializers.get_sub())
    {
      irept &initializer=*m_it;

      if(initializer.get(ID_member)!=ID_cpp_name)
        continue;
      cpp_namet &member_name=(cpp_namet&) initializer.add(ID_member);

      if(member_name.has_template_args())
        continue; // base-type initializer

      irep_idt base_name=member_name.get_base_name();

      if(mem_name==base_name)
      {
        final_initializers.move_to_sub(initializer);
        found=true;
        break;
      }
    }

    // If the data member is a reference, it must be explicitly
    // initialized
    if(
      !found && c.find(ID_type).id() == ID_pointer &&
      c.find(ID_type).get_bool(ID_C_reference))
    {
      error().source_location = c.source_location();
      error() << "reference must be explicitly initialized" << eom;
      throw 0;
    }

    // If the data member is not POD and is not explicitly initialized,
    // then its default constructor is called.
    if(!found && !cpp_is_pod((const typet &)(c.find(ID_type))))
    {
      cpp_namet cppname(mem_name);

      codet mem_init(ID_member_initializer);
      mem_init.set(ID_member, cppname);
      final_initializers.move_to_sub(mem_init);
    }
  }

  initializers.swap(final_initializers);
}

/// \par parameters: typechecked compound symbol
/// \return return true if a copy constructor is found
bool cpp_typecheckt::find_cpctor(const symbolt &symbol) const
{
  const struct_typet &struct_type=to_struct_type(symbol.type);
  const struct_typet::componentst &components=struct_type.components();

  for(struct_typet::componentst::const_iterator
      cit=components.begin();
      cit!=components.end();
      cit++)
  {
    // Skip non-ctor
    const struct_typet::componentt &component=*cit;

    if(component.type().id()!=ID_code ||
       to_code_type(component.type()).return_type().id() !=ID_constructor)
      continue;

    // Skip inherited constructor
    if(component.get_bool(ID_from_base))
      continue;

    const code_typet &code_type=to_code_type(component.type());

    const code_typet::parameterst &parameters=code_type.parameters();

    // First parameter is the 'this' pointer. Therefore, copy
    // constructors have at least two parameters
    if(parameters.size() < 2)
      continue;

    const code_typet::parametert &parameter1=parameters[1];

    const typet &parameter1_type=parameter1.type();

    if(!is_reference(parameter1_type))
      continue;

    if(parameter1_type.subtype().get(ID_identifier)!=symbol.name)
      continue;

    bool defargs=true;
    for(std::size_t i=2; i<parameters.size(); i++)
    {
      if(parameters[i].default_value().is_nil())
      {
        defargs=false;
        break;
      }
    }

    if(defargs)
      return true;
  }

  return false;
}

bool cpp_typecheckt::find_assignop(const symbolt &symbol) const
{
  const struct_typet &struct_type=to_struct_type(symbol.type);
  const struct_typet::componentst &components=struct_type.components();

  for(const auto &component : components)
  {
    if(component.get_base_name() != "operator=")
      continue;

    if(component.get_bool(ID_is_static))
      continue;

    if(component.get_bool(ID_from_base))
       continue;

    const code_typet &code_type=to_code_type(component.type());

    const code_typet::parameterst &args=code_type.parameters();

    if(args.size()!=2)
      continue;

    const code_typet::parametert &arg1=args[1];

    const typet &arg1_type=arg1.type();

    if(!is_reference(arg1_type))
      continue;

    if(arg1_type.subtype().get(ID_identifier)!=symbol.name)
      continue;

    return true;
  }

  return false;
}
