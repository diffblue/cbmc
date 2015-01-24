/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>

#include "cpp_typecheck.h"
#include "cpp_util.h"

/*******************************************************************\

Function: copy_parent

  Inputs: parent_base_name: base name of typechecked parent
          block: non-typechecked block

 Outputs: generate code to copy the parent

 Purpose:

\*******************************************************************/

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
  op0.type().id(ID_pointer);
  op0.type().subtype()=cpp_namet(parent_base_name, source_location).as_type();
  op0.add_source_location() = source_location;

  code.operands().push_back(exprt("explicit-typecast"));
  exprt &op1 = code.op1();

  op1.type().id(ID_pointer);
  op1.type().set(ID_C_reference, true);
  op1.type().subtype().set(ID_C_constant, true);
  op1.type().subtype()=cpp_namet(parent_base_name, source_location).as_type();

  op1.operands().push_back(exprt(ID_cpp_name));
  op1.op0().get_sub().push_back(irept(ID_name));
  op1.op0().get_sub().back().set(ID_identifier, arg_name);
  op1.op0().get_sub().back().set(ID_C_source_location, source_location);
  op1.add_source_location() = source_location;
}

/*******************************************************************\

Function: copy_member

  Inputs: member_base_name: name of a member
          block: non-typechecked block

 Outputs: generate code to copy the member

 Purpose:

\*******************************************************************/

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
  code.add_source_location() = source_location;

  exprt &op0 = code.op0().op0();
  op0.add_source_location() = source_location;

  op0.get_sub().push_back(irept(ID_name));
  op0.get_sub().back().set(ID_identifier, member_base_name);
  op0.get_sub().back().set(ID_C_source_location, source_location);

  code.op0().operands().push_back(exprt(ID_member));

  exprt &op1 = code.op0().op1();

  op1.add("component_cpp_name").id(ID_cpp_name);
  op1.add("component_cpp_name").get_sub().push_back(irept(ID_name));
  op1.add("component_cpp_name").get_sub().back().set(ID_identifier, member_base_name);
  op1.add("component_cpp_name").get_sub().back().set(ID_C_source_location, source_location);

  op1.operands().push_back(exprt(ID_cpp_name));
  op1.op0().get_sub().push_back(irept(ID_name));
  op1.op0().get_sub().back().set(ID_identifier, arg_name);
  op1.op0().get_sub().back().set(ID_C_source_location, source_location);
  op1.add_source_location() = source_location;
}

/*******************************************************************\

Function: copy_array

  Inputs: member_base_name: name of array member
          index: index to copy
          block: non-typechecked block

 Outputs: generate code to copy the member

 Purpose:

\*******************************************************************/

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
  exprt& code = block.operands().back();
  code.add_source_location() = source_location;

  code.set(ID_statement, ID_expression);
  code.add(ID_type)=typet(ID_code);
  code.operands().push_back(exprt(ID_side_effect));
  code.op0().set(ID_statement, ID_assign);
  code.op0().operands().push_back(exprt(ID_index));
  exprt& op0 = code.op0().op0();
  op0.operands().push_back(exprt(ID_cpp_name));
  op0.add_source_location() = source_location;

  op0.op0().get_sub().push_back(irept(ID_name));
  op0.op0().get_sub().back().set(ID_identifier, member_base_name);
  op0.op0().get_sub().back().set(ID_C_source_location, source_location);
  op0.copy_to_operands(constant);

  code.op0().operands().push_back(exprt(ID_index));

  exprt& op1 = code.op0().op1();
  op1.operands().push_back(exprt(ID_member));
  op1.op0().add("component_cpp_name").id(ID_cpp_name);
  op1.op0().add("component_cpp_name").get_sub().push_back(irept(ID_name));
  op1.op0().add("component_cpp_name").get_sub().back().set(ID_identifier, member_base_name);
  op1.op0().add("component_cpp_name").get_sub().back().set(ID_C_source_location, source_location);

  op1.op0().operands().push_back(exprt(ID_cpp_name));
  op1.op0().op0().get_sub().push_back(irept(ID_name));
  op1.op0().op0().get_sub().back().set(ID_identifier, arg_name);
  op1.op0().op0().get_sub().back().set(ID_C_source_location, source_location);
  op1.copy_to_operands(constant);

  op1.add_source_location() = source_location;
}

/*******************************************************************\

Function: cpp_typecheckt::default_ctor

  Inputs:

 Outputs:

 Purpose: Generate code for implicit default constructors

\*******************************************************************/

void cpp_typecheckt::default_ctor(
  const source_locationt &source_location,
  const irep_idt &base_name,
  cpp_declarationt &ctor) const
{
  exprt name(ID_name);
  name.set(ID_identifier, base_name);
  name.add_source_location() = source_location;

  cpp_declaratort decl;
  decl.name().id(ID_cpp_name);
  decl.name().move_to_sub(name);
  decl.type()=typet("function_type");
  decl.type().subtype().make_nil();
  decl.add_source_location() = source_location;

  decl.value().id(ID_code);
  decl.value().type()=typet(ID_code);
  decl.value().set(ID_statement, ID_block);
  decl.add("cv").make_nil();
  decl.add("throw_decl").make_nil();

  ctor.type().id(ID_constructor);
  ctor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  ctor.move_to_operands(decl);
  ctor.add_source_location() = source_location;
}

/*******************************************************************\

Function: cpp_typecheckt::default_cpctor

  Inputs:

 Outputs:

 Purpose: Generate code for implicit default copy constructor

\*******************************************************************/

void cpp_typecheckt::default_cpctor(
  const symbolt &symbol,
  cpp_declarationt &cpctor) const
{
  source_locationt source_location = symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)+
    "::"+id2string(symbol.base_name)+
    "(const "+id2string(symbol.base_name)+" &)");

  // Produce default constructor first
  default_ctor(source_location, symbol.base_name, cpctor);
  cpp_declaratort &decl0 = cpctor.declarators()[0];

  std::string param_identifier("ref");

  // Compound name
  irept comp_name(ID_name);
  comp_name.set(ID_identifier, symbol.base_name);
  comp_name.set(ID_C_source_location, source_location);

  cpp_namet cppcomp;
  cppcomp.move_to_sub(comp_name);

  // Parameter name
  exprt param_name(ID_name);
  param_name.add_source_location()=source_location;
  param_name.set(ID_identifier, param_identifier);
  
  cpp_namet cpp_parameter;
  cpp_parameter.move_to_sub(param_name);

  // Parameter declarator
  cpp_declaratort parameter_tor;
  parameter_tor.add(ID_value).make_nil();
  parameter_tor.set(ID_name, cpp_parameter);
  parameter_tor.type()=reference_typet();
  parameter_tor.type().subtype().make_nil();
  parameter_tor.type().add(ID_C_qualifier).make_nil();
  parameter_tor.add_source_location() = source_location;

  // Parameter declaration
  cpp_declarationt parameter_decl;
  parameter_decl.set(ID_type, ID_merged_type);
  typet::subtypest &sub = parameter_decl.type().subtypes();
  sub.push_back((const typet &)(cppcomp));
  irept constnd(ID_const);
  sub.push_back((const typet &)(constnd));
  parameter_decl.move_to_operands(parameter_tor);
  parameter_decl.add_source_location() = source_location;

  // Add parameter to function type
  decl0.add(ID_type).add(ID_parameters).get_sub().push_back(parameter_decl);
  decl0.add_source_location() = source_location;

  irept &initializers = decl0.add(ID_member_initializers);
  initializers.id(ID_member_initializers);

  cpp_declaratort &declarator = (cpp_declaratort &) cpctor.op0();
  exprt &block = declarator.value();

  // First, we need to call the parent copy constructors
  const irept &bases = symbol.type.find(ID_bases);
  forall_irep(parent_it, bases.get_sub())
  {
    assert(parent_it->id() == ID_base);
    assert(parent_it->get(ID_type) == ID_symbol);

    const symbolt &parsymb=
      lookup(parent_it->find(ID_type).get(ID_identifier));

    if(cpp_is_pod(parsymb.type))
      copy_parent(source_location, parsymb.base_name, param_identifier, block);
    else
    {
      irep_idt ctor_name = parsymb.base_name;

      // Call the parent default copy constructor
      exprt name(ID_name);
      name.set(ID_identifier, ctor_name);
      name.add_source_location() = source_location;

      cpp_namet cppname;
      cppname.move_to_sub(name);

      codet mem_init(ID_member_initializer);
      mem_init.add_source_location() = source_location;
      mem_init.set(ID_member, cppname);
      mem_init.copy_to_operands(static_cast<const exprt &>(static_cast<const irept &>(cpp_parameter)));
      initializers.move_to_sub(mem_init);
    }
  }

  // Then, we add the member initializers
  const struct_typet::componentst& components = to_struct_type(symbol.type).components();
  for(struct_typet::componentst::const_iterator mem_it = components.begin();
      mem_it != components.end(); mem_it++)
  {
    // Take care of virtual tables
    if(mem_it->get_bool("is_vtptr"))
    {
      exprt name(ID_name);
      name.set(ID_identifier,mem_it->get(ID_base_name));
      name.add_source_location()=source_location;
      
      cpp_namet cppname;
      cppname.move_to_sub(name);

      const symbolt &virtual_table_symbol_type = 
        namespacet(symbol_table).lookup(mem_it->type().subtype().get(ID_identifier));

      const symbolt &virtual_table_symbol_var  =
        namespacet(symbol_table).lookup(id2string(virtual_table_symbol_type.name) + "@" +
        id2string(symbol.name));

      exprt var = virtual_table_symbol_var.symbol_expr();
      address_of_exprt address(var);
      assert(address.type() == mem_it->type());

      already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, mem_it->get(ID_name));
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_assignt assign(ptrmember, address);
      initializers.move_to_sub(assign);
      continue;
    }

    if( mem_it->get_bool("from_base")
      || mem_it->get_bool(ID_is_type)
      || mem_it->get_bool(ID_is_static)
      || mem_it->type().id() == ID_code)
        continue;

    irep_idt mem_name = mem_it->get(ID_base_name);

    exprt name(ID_name);
    name.set(ID_identifier, mem_name);
    name.add_source_location() = source_location;

    cpp_namet cppname;
    cppname.move_to_sub(name);

    codet mem_init(ID_member_initializer);
    mem_init.set(ID_member, cppname);
    mem_init.add_source_location() = source_location;

    exprt memberexpr(ID_member);
    memberexpr.set("component_cpp_name", cppname);
    memberexpr.copy_to_operands(static_cast<const exprt &>(static_cast<const irept &>(cpp_parameter)));
    memberexpr.add_source_location() = source_location;

    if(mem_it->type().id()==ID_array)
      memberexpr.set("#array_ini", true);

    mem_init.move_to_operands(memberexpr);
    initializers.move_to_sub(mem_init);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::default_assignop

  Inputs:

 Outputs:

 Purpose: Generate declarartion of the implicit default assignment
          operator

\*******************************************************************/

void cpp_typecheckt::default_assignop(
  const symbolt& symbol,
  cpp_declarationt& cpctor)
{
  source_locationt source_location = symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)
    + "& "+
    id2string(symbol.base_name)+
    "::operator=( const "+id2string(symbol.base_name)+"&)");

  std::string arg_name("ref");

  cpctor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  cpctor.type().id(ID_symbol);
  cpctor.type().add(ID_identifier).id(symbol.name);
  cpctor.operands().push_back(exprt(ID_cpp_declarator));
  cpctor.add_source_location() = source_location;

  cpp_declaratort &declarator = (cpp_declaratort&) cpctor.op0();
  declarator.add_source_location() = source_location;

  cpp_namet &declarator_name = declarator.name();
  typet &declarator_type = declarator.type();

  declarator_type.add_source_location() = source_location;

  declarator_name.id(ID_cpp_name);
  declarator_name.get_sub().push_back(irept(ID_operator));
  declarator_name.get_sub().push_back(irept("="));

  declarator_type.id("function_type");
  declarator_type.subtype()=reference_typet();
  declarator_type.subtype().add("#qualifier").make_nil();
  declarator_type.subtype().subtype().make_nil();

  exprt& args = (exprt&) declarator.type().add(ID_parameters);
  args.add_source_location() = source_location;

  args.get_sub().push_back(irept(ID_cpp_declaration));

  cpp_declarationt& args_decl = (cpp_declarationt&) args.get_sub().back();

  typet::subtypest & args_decl_type_sub = args_decl.type().subtypes();

  args_decl.type().id(ID_merged_type);
  args_decl_type_sub.push_back(typet(ID_cpp_name));
  args_decl_type_sub.back().get_sub().push_back(irept(ID_name));
  args_decl_type_sub.back().get_sub().back().set(ID_identifier, symbol.base_name);
  args_decl_type_sub.back().get_sub().back().set(ID_C_source_location, source_location);

  args_decl_type_sub.push_back(typet(ID_const));
  args_decl.operands().push_back(exprt(ID_cpp_declarator));
  args_decl.add_source_location() = source_location;

  cpp_declaratort &args_decl_declor=
    (cpp_declaratort&) args_decl.operands().back();

  args_decl_declor.name().id(ID_cpp_name);
  args_decl_declor.name().get_sub().push_back(irept(ID_name));
  args_decl_declor.name().get_sub().back().add(ID_identifier).id(arg_name);
  args_decl_declor.add_source_location() = source_location;

  args_decl_declor.type().id(ID_pointer);
  args_decl_declor.type().set(ID_C_reference, true);
  args_decl_declor.type().add(ID_C_qualifier).make_nil();
  args_decl_declor.type().subtype().make_nil();
  args_decl_declor.value().make_nil();
}

/*******************************************************************\

Function: cpp_typecheckt::default_assignop_value

  Inputs:

 Outputs:

 Purpose: Generate code for the implicit default assignment operator

\*******************************************************************/

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
  declarator.value().type()=code_typet();

  exprt &block=declarator.value();

  std::string arg_name("ref");

  // First, we copy the parents
  const irept &bases = symbol.type.find(ID_bases);

  forall_irep(parent_it, bases.get_sub())
  {
    assert(parent_it->id() == ID_base);
    assert(parent_it->get(ID_type) == ID_symbol);

    const symbolt &symb=
      lookup(parent_it->find(ID_type).get(ID_identifier));

    copy_parent(source_location, symb.base_name, arg_name, block);
  }

  // Then, we copy the members
  const irept &components=symbol.type.find(ID_components);

  forall_irep(mem_it, components.get_sub())
  {
    if(mem_it->get_bool(ID_from_base) ||
       mem_it->get_bool(ID_is_type) ||
       mem_it->get_bool(ID_is_static) ||
       mem_it->get_bool("is_vtptr") ||
       mem_it->get(ID_type)==ID_code)
      continue;

    irep_idt mem_name=mem_it->get(ID_base_name);

    if(mem_it->get(ID_type)==ID_array)
    {
      const exprt &size_expr=
        to_array_type((typet&)mem_it->find(ID_type)).size();

      if(size_expr.id()==ID_infinity)
      {
        // err_location(object);
        // err << "cannot copy array of infinite size" << std::endl;
        // throw 0;
        continue;
      }
  
      mp_integer size;
      bool to_int = to_integer(size_expr, size);
      assert(!to_int);
      assert(size>=0);

      exprt::operandst empty_operands;
      for(mp_integer i = 0; i < size; ++i)
        copy_array(source_location, mem_name,i,arg_name,block);
    }
    else
      copy_member(source_location, mem_name, arg_name, block);
  }

  // Finally we add the return statement
  block.operands().push_back(exprt(ID_code));
  exprt &ret_code = declarator.value().operands().back();
  ret_code.operands().push_back(exprt(ID_dereference));
  ret_code.op0().operands().push_back(exprt("cpp-this"));
  ret_code.set(ID_statement, ID_return);
  ret_code.type()=code_typet();
}

/*******************************************************************\

Function: check_member_initializers

  Inputs: bases: the parents of the class
          components: the components of the class
          initializers: the constructor initializers

 Outputs: If an invalid initializer is found, then
          the method outputs an error message and
          throws a 0 exception.

 Purpose: Check a constructor initialization-list.
          An initalizer has to be a data member declared
          in this class or a direct-parent constructor.

\*******************************************************************/

void cpp_typecheckt::check_member_initializers(
  const irept &bases,
  const struct_typet::componentst &components,
  const irept &initializers)
{
  assert(initializers.id() == ID_member_initializers);

  forall_irep(init_it, initializers.get_sub())
  {
    const irept &initializer = *init_it;
    assert(initializer.is_not_nil());

    assert(initializer.get(ID_member) == ID_cpp_name);

    const cpp_namet &member_name=
      to_cpp_name(initializer.find(ID_member));

    bool has_template_args = member_name.has_template_args();

    if(has_template_args)
    {
      // it has to be a parent constructor
      typet member_type = (typet&) initializer.find(ID_member);
      typecheck_type(member_type);

      // check for a direct parent
      bool ok = false;
      forall_irep(parent_it, bases.get_sub())
      {
        assert(parent_it->get(ID_type) == ID_symbol);

        if(member_type.get(ID_identifier)
           == parent_it->find(ID_type).get(ID_identifier))
        {
          ok = true;
          break;
        }
      }

      if(!ok)
      {
        err_location(member_name.source_location());
        str << "invalid initializer `" << member_name.to_string() << "'";
        throw 0;
      }
      return;
    }

    irep_idt base_name=member_name.get_base_name();
    bool ok = false;

    for(struct_typet::componentst::const_iterator
        c_it=components.begin();
        c_it!=components.end();
        c_it++)
    {
      if(c_it->get(ID_base_name)!=base_name ) continue;

      // Data member
      if(!c_it->get_bool(ID_from_base) &&
         !c_it->get_bool(ID_is_static) &&
         c_it->get(ID_type) != ID_code)
      {
        ok = true;
        break;
      }

      // Maybe it is a parent constructor?
      if(c_it->get_bool("is_type"))
      {
        typet type = static_cast<const typet&>(c_it->find(ID_type));
        if(type.id() != ID_symbol)
          continue;

        const symbolt& symb = lookup(type.get(ID_identifier));
        if(symb.type.id() != ID_struct)
          break;

        // check for a direct parent
        forall_irep(parent_it, bases.get_sub())
        {
          assert(parent_it->get(ID_type) == ID_symbol );
          if(symb.name == parent_it->find(ID_type).get(ID_identifier))
          {
            ok = true;
            break;
          }
        }
        continue;
      }

      // Parent constructor
      if( c_it->get_bool(ID_from_base)
        && !c_it->get_bool(ID_is_type)
        && !c_it->get_bool(ID_is_static)
        && c_it->get(ID_type) == ID_code
        && c_it->find(ID_type).get(ID_return_type) == ID_constructor)
      {
        typet member_type = (typet&) initializer.find(ID_member);
        typecheck_type(member_type);

        // check for a direct parent
        forall_irep(parent_it, bases.get_sub())
        {
          assert(parent_it->get(ID_type) == ID_symbol );

          if(member_type.get(ID_identifier)
             == parent_it->find(ID_type).get(ID_identifier))
          {
            ok = true;
            break;
          }
        }
        break;
      }
    }

    if(!ok)
    {
      err_location(member_name.source_location());
      str << "invalid initializer `" << base_name << "'";
      throw 0;
    }
  }
}

/*******************************************************************\

Function: full_member_initialization

  Inputs: struct_union_type: the class/struct/union
          initializers: the constructor initializers

 Outputs: initializers is updated.

 Purpose: Build the full initialization list of the constructor.
          First, all the direct-parent constructors are called.
          Second, all the non-pod data members are initialized.

    Note: The initialization order follows the decalration order.

\*******************************************************************/

void cpp_typecheckt::full_member_initialization(
  const struct_union_typet &struct_union_type,
  irept &initializers)
{
  const struct_union_typet::componentst &components=
    struct_union_type.components();

  assert(initializers.id() == ID_member_initializers);

  irept final_initializers(ID_member_initializers);

  if(struct_union_type.id()==ID_struct)
  {
    // First, if we are the most-derived object, then
    // we need to construct the virtual bases
    std::list<irep_idt> vbases;
    get_virtual_bases(to_struct_type(struct_union_type), vbases);

    if(!vbases.empty())
    {
      codet cond(ID_ifthenelse);

      {
        cpp_namet most_derived;
        most_derived.get_sub().push_back(irept(ID_name));
        most_derived.get_sub().back().set(ID_identifier, "@most_derived");

        exprt tmp;
        tmp.swap(most_derived);
        cond.move_to_operands(tmp);
      }

      codet block(ID_block);

      while(!vbases.empty())
      {
        const symbolt& symb = lookup(vbases.front());
        if(!cpp_is_pod(symb.type))
        {
          // default initializer
          irept name(ID_name);
          name.set(ID_identifier, symb.base_name);

          cpp_namet cppname;
          cppname.move_to_sub(name);

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

    // Subsequenlty, we need to call the non-POD parent constructors
    forall_irep(parent_it, bases.get_sub())
    {
      assert(parent_it->id() == ID_base);
      assert(parent_it->get(ID_type) == ID_symbol);

      const symbolt &ctorsymb=
        lookup(parent_it->find(ID_type).get(ID_identifier));

      if(cpp_is_pod(ctorsymb.type))
        continue;

      irep_idt ctor_name=ctorsymb.base_name;

      // Check if the initialization list of the constructor
      // explicitly calls the parent constructor.
      bool found = false;

      forall_irep(m_it, initializers.get_sub())
      {
        irept initializer = *m_it;

        assert(initializer.get(ID_member) == ID_cpp_name);

        const cpp_namet &member_name=
          to_cpp_name(initializer.find(ID_member));

        bool has_template_args = member_name.has_template_args();

        if(!has_template_args)
        {
          irep_idt base_name=member_name.get_base_name();

          // check if the initializer is a data
          bool is_data = false;

          for(struct_typet::componentst::const_iterator c_it =
              components.begin(); c_it != components.end(); c_it++)
          {
            if(c_it->get(ID_base_name)==base_name && 
               c_it->get(ID_type)!=ID_code &&
               !c_it->get_bool(ID_is_type))
            {
              is_data = true;
              break;
            }
          }

          if(is_data)
            continue;
        }

        typet member_type=
          static_cast<const typet&>(initializer.find(ID_member));

        typecheck_type(member_type);

        if(member_type.id()!=ID_symbol)
          break;

        if(parent_it->find(ID_type).get(ID_identifier)==
           member_type.get(ID_identifier))
        {
          final_initializers.move_to_sub(initializer);
          found = true;
          break;
        }
      }

      // Call the parent default constructor
      if(!found)
      {
        irept name(ID_name);
        name.set(ID_identifier, ctor_name);

        cpp_namet cppname;
        cppname.move_to_sub(name);

        codet mem_init(ID_member_initializer);
        mem_init.set(ID_member, cppname);
        final_initializers.move_to_sub(mem_init);
      }

      if(parent_it->get_bool(ID_virtual))
      {
        codet cond(ID_ifthenelse);

        {
          cpp_namet most_derived;
          most_derived.get_sub().push_back(irept(ID_name));
          most_derived.get_sub().back().set(ID_identifier, "@most_derived");

          exprt tmp;
          tmp.swap(most_derived);
          cond.move_to_operands(tmp);
        }

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
  for(struct_typet::componentst::const_iterator mem_it =
      components.begin(); mem_it != components.end(); mem_it++)
  {
    // Take care of virtual tables
    if(mem_it->get_bool("is_vtptr"))
    {
      exprt name(ID_name);
      name.set(ID_identifier,mem_it->get(ID_base_name));
      name.add_source_location() = mem_it->source_location();

      cpp_namet cppname;
      cppname.move_to_sub(name);

      const symbolt& virtual_table_symbol_type = 
        lookup(mem_it->type().subtype().get(ID_identifier));

      const symbolt& virtual_table_symbol_var  =
        lookup(id2string(virtual_table_symbol_type.name) + "@" + 
            id2string(struct_union_type.get(ID_name)));

      exprt var = virtual_table_symbol_var.symbol_expr();
      address_of_exprt address(var);
      assert(address.type() == mem_it->type());

      already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, mem_it->get(ID_name));
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_assignt assign(ptrmember, address);
      final_initializers.move_to_sub(assign);
      continue;
    }

    if( mem_it->get_bool(ID_from_base)
      || mem_it->type().id() == ID_code
      || mem_it->get_bool(ID_is_type)
      || mem_it->get_bool(ID_is_static))
        continue;

    irep_idt mem_name = mem_it->get(ID_base_name);

    // Check if the initialization list of the constructor
    // explicitly initializes the data member
    bool found = false;
    Forall_irep(m_it, initializers.get_sub())
    {
      irept &initializer = *m_it;

      if(initializer.get(ID_member)!=ID_cpp_name) continue;
      cpp_namet &member_name=(cpp_namet&) initializer.add(ID_member);

      if(member_name.has_template_args())
        continue; // base-type initializer

      irep_idt base_name=member_name.get_base_name();

      if(mem_name==base_name)
      {
        final_initializers.move_to_sub(initializer);
        found = true;
        break;
      }
    }

    // If the data member is a reference, it must be explicitly
    // initialized
    if(!found &&
       mem_it->find(ID_type).id()==ID_pointer &&
       mem_it->find(ID_type).get_bool(ID_C_reference))
    {
      err_location(*mem_it);
      str << "reference must be explicitly initialized";
      throw 0;
    }

    // If the data member is not POD and is not explicitly initialized,
    // then its default constructor is called.
    if(!found && !cpp_is_pod((const typet &)(mem_it->find(ID_type))))
    {
      irept name(ID_name);
      name.set(ID_identifier, mem_name);

      cpp_namet cppname;
      cppname.move_to_sub(name);

      codet mem_init(ID_member_initializer);
      mem_init.set(ID_member, cppname);
      final_initializers.move_to_sub(mem_init);
    }
  }

  initializers.swap(final_initializers);
}

/*******************************************************************\

Function: find_cpctor

  Inputs: typechecked compound symbol

 Outputs: return true if a copy constructor is found

  Note:
    "A non-template constructor for class X is a copy constructor
    if its first parameter is of type X&, const X&, volatile X&
    or const volatile X&, and either there are no other parameters
    or else all other parameters have default arguments (8.3.6).106)
    [Example: X::X(const X&) and X::X(X&, int=1) are copy constructors."

\*******************************************************************/

bool cpp_typecheckt::find_cpctor(const symbolt &symbol) const
{
  const struct_typet &struct_type = to_struct_type(symbol.type);
  const struct_typet::componentst &components = struct_type.components();

  for(struct_typet::componentst::const_iterator
      cit=components.begin();
      cit!=components.end();
      cit++)
  {
    // Skip non-ctor
    const struct_typet::componentt& component = *cit;

    if(component.type().id() != ID_code
      || to_code_type(component.type()).return_type().id() !=ID_constructor)
      continue;

    // Skip inherited constructor
    if(component.get_bool(ID_from_base))
      continue;

    const code_typet& code_type = to_code_type(component.type());

    const code_typet::parameterst &parameters=code_type.parameters();

    // First parameter is the 'this' pointer. Therefore, copy
    // constructors have at least two parameters
    if(parameters.size() < 2)
      continue;

    const code_typet::parametert &parameter1 = parameters[1];

    const typet &parameter1_type=parameter1.type();

    if(!is_reference(parameter1_type))
      continue;

    if(parameter1_type.subtype().get(ID_identifier)!=symbol.name)
      continue;

    bool defargs = true;
    for(unsigned i=2; i<parameters.size(); i++)
    {
      if(parameters[i].default_value().is_nil())
      {
        defargs=false;
        break;
      }
    }

    if(defargs) return true;
  }

  return false;
}

/*******************************************************************\

Function: cpp_typecheckt::find_assignop

  Inputs:

 Outputs:

    Note:

\*******************************************************************/

bool cpp_typecheckt::find_assignop(const symbolt& symbol) const
{
  const struct_typet& struct_type = to_struct_type(symbol.type);
  const struct_typet::componentst& components = struct_type.components();

  for(unsigned i = 0; i < components.size(); i++)
  {
    const struct_typet::componentt& component = components[i];

    if(component.get(ID_base_name)!="operator=")
      continue;

    if(component.get_bool(ID_is_static))
      continue;

    if(component.get_bool(ID_from_base))
       continue;

    const code_typet&  code_type = to_code_type(component.type());

    const code_typet::parameterst& args = code_type.parameters();

    if(args.size()!=2)
      continue;

    const code_typet::parametert& arg1 = args[1];

    const typet &arg1_type= arg1.type();

    if(!is_reference(arg1_type))
      continue;

    if(arg1_type.subtype().get(ID_identifier)!=symbol.name)
      continue;

    return true;
  }

  return false;
}

