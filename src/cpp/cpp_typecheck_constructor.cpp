/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

/// Generate code to copy the parent.
/// \param source_location: location for generated code
/// \param parent_base_name: base name of typechecked parent
/// \param arg_name: name of argument that is being copied
/// \param [out] block: non-typechecked block
static void copy_parent(
  const source_locationt &source_location,
  const irep_idt &parent_base_name,
  const irep_idt &arg_name,
  exprt &block)
{
  exprt op0(
    "explicit-typecast",
    pointer_type(cpp_namet(parent_base_name, source_location).as_type()));
  op0.copy_to_operands(exprt("cpp-this"));
  op0.add_source_location()=source_location;

  exprt op1(
    "explicit-typecast",
    pointer_type(cpp_namet(parent_base_name, source_location).as_type()));
  op1.type().set(ID_C_reference, true);
  to_pointer_type(op1.type()).base_type().set(ID_C_constant, true);
  op1.get_sub().push_back(cpp_namet(arg_name, source_location));
  op1.add_source_location()=source_location;

  code_frontend_assignt code(dereference_exprt(op0), op1);
  code.add_source_location() = source_location;

  block.operands().push_back(code);
}

/// Generate code to copy the member.
/// \param source_location: location for generated code
/// \param member_base_name: name of a member
/// \param arg_name: name of argument that is being copied
/// \param [out] block: non-typechecked block
static void copy_member(
  const source_locationt &source_location,
  const irep_idt &member_base_name,
  const irep_idt &arg_name,
  exprt &block)
{
  cpp_namet op0(member_base_name, source_location);

  exprt op1(ID_member);
  op1.add(ID_component_cpp_name, cpp_namet(member_base_name, source_location));
  op1.copy_to_operands(cpp_namet(arg_name, source_location).as_expr());
  op1.add_source_location()=source_location;

  side_effect_expr_assignt assign(op0.as_expr(), op1, typet(), source_location);
  assign.lhs().add_source_location() = source_location;

  code_expressiont code(assign);
  code.add_source_location() = source_location;

  block.operands().push_back(code);
}

/// Generate code to copy the member.
/// \param source_location: location for generated code
/// \param member_base_name: name of array member
/// \param i: index to copy
/// \param arg_name: name of argument that is being copied
/// \param [out] block: non-typechecked block
static void copy_array(
  const source_locationt &source_location,
  const irep_idt &member_base_name,
  mp_integer i,
  const irep_idt &arg_name,
  exprt &block)
{
  // Build the index expression
  const exprt constant = from_integer(i, c_index_type());

  const cpp_namet array(member_base_name, source_location);

  exprt member(ID_member);
  member.add(
    ID_component_cpp_name, cpp_namet(member_base_name, source_location));
  member.copy_to_operands(cpp_namet(arg_name, source_location).as_expr());

  side_effect_expr_assignt assign(
    binary_exprt(array.as_expr(), ID_index, constant, typet()),
    binary_exprt(member, ID_index, constant, typet()),
    typet(),
    source_location);

  assign.lhs().add_source_location() = source_location;
  assign.rhs().add_source_location() = source_location;

  code_expressiont code(assign);
  code.add_source_location() = source_location;

  block.operands().push_back(code);
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
  decl.type().add_subtype().make_nil();
  decl.add_source_location()=source_location;

  decl.value() = code_blockt();
  decl.add(ID_cv).make_nil();
  decl.add(ID_throw_decl).make_nil();

  ctor.type().id(ID_constructor);
  ctor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  ctor.add_to_operands(std::move(decl));
  ctor.add_source_location()=source_location;
}

/// Generate code for implicit default copy constructor
void cpp_typecheckt::default_cpctor(
  const symbolt &symbol,
  cpp_declarationt &cpctor,
  const irep_idt &param_identifier_arg) const
{
  source_locationt source_location=symbol.type.source_location();

  source_location.set_function(
    id2string(symbol.base_name)+
    "::"+id2string(symbol.base_name)+
    "(const "+id2string(symbol.base_name)+" &)");

  // Produce default constructor first
  default_ctor(source_location, symbol.base_name, cpctor);
  cpp_declaratort &decl0=cpctor.declarators()[0];

  std::string param_identifier(id2string(param_identifier_arg));

  // Compound name
  const cpp_namet cppcomp(symbol.base_name, source_location);

  // Parameter name
  const cpp_namet cpp_parameter(param_identifier, source_location);

  // Parameter declarator
  cpp_declaratort parameter_tor;
  parameter_tor.add(ID_value).make_nil();
  parameter_tor.set(ID_name, cpp_parameter);
  parameter_tor.type() = reference_type(uninitialized_typet{});
  parameter_tor.add_source_location()=source_location;

  // Parameter declaration
  cpp_declarationt parameter_decl;
  parameter_decl.set(ID_type, ID_merged_type);
  auto &sub = to_type_with_subtypes(parameter_decl.type()).subtypes();
  sub.push_back(cppcomp.as_type());
  irept constnd(ID_const);
  sub.push_back(static_cast<const typet &>(constnd));
  parameter_decl.add_to_operands(std::move(parameter_tor));
  parameter_decl.add_source_location()=source_location;

  // Add parameter to function type
  decl0.add(ID_type).add(ID_parameters).get_sub().push_back(parameter_decl);
  decl0.add_source_location()=source_location;

  irept &initializers=decl0.add(ID_member_initializers);
  initializers.id(ID_member_initializers);

  // First, we need to call the parent copy constructors
  for(const auto &b : to_struct_type(symbol.type).bases())
  {
    DATA_INVARIANT(b.id() == ID_base, "base class expression expected");

    const symbolt &parsymb = lookup(b.type());

    if(cpp_is_pod(parsymb.type))
    {
      // For POD bases, generate a direct assignment as an initializer
      // so it runs before member copies (correct C++ init order).
      exprt op0(
        "explicit-typecast",
        pointer_type(cpp_namet(parsymb.base_name, source_location).as_type()));
      op0.copy_to_operands(exprt("cpp-this"));
      op0.add_source_location() = source_location;

      exprt op1(
        "explicit-typecast",
        pointer_type(cpp_namet(parsymb.base_name, source_location).as_type()));
      op1.type().set(ID_C_reference, true);
      to_pointer_type(op1.type()).base_type().set(ID_C_constant, true);
      op1.get_sub().push_back(cpp_namet(param_identifier, source_location));
      op1.add_source_location() = source_location;

      code_frontend_assignt assign_code(dereference_exprt(op0), op1);
      assign_code.add_source_location() = source_location;
      initializers.move_to_sub(assign_code);
    }
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

      const symbolt *virtual_table_symbol_type;
      if(lookup(
           to_pointer_type(mem_c.type()).base_type().get(ID_identifier),
           virtual_table_symbol_type))
        continue;

      const symbolt *virtual_table_symbol_var;
      if(lookup(
           id2string(virtual_table_symbol_type->name) + "@" +
             id2string(symbol.name),
           virtual_table_symbol_var))
        continue;

      exprt var = virtual_table_symbol_var->symbol_expr();
      address_of_exprt address(var);
      CHECK_RETURN(address.type() == mem_c.type());

      already_typechecked_exprt::make_already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, mem_c.get_name());
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_frontend_assignt assign(ptrmember, address);
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

    mem_init.add_to_operands(std::move(memberexpr));
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
  cpctor.type().id(ID_struct_tag);
  cpctor.type().add(ID_identifier).id(symbol.name);
  cpctor.operands().push_back(exprt(ID_cpp_declarator));
  cpctor.add_source_location()=source_location;

  cpp_declaratort &declarator =
    static_cast<cpp_declaratort &>(to_multi_ary_expr(cpctor).op0());
  declarator.add_source_location()=source_location;

  cpp_namet &declarator_name=declarator.name();
  typet &declarator_type=declarator.type();

  declarator_type.add_source_location()=source_location;

  declarator_name.id(ID_cpp_name);
  declarator_name.get_sub().push_back(irept(ID_operator));
  declarator_name.get_sub().push_back(irept("="));

  declarator_type.id(ID_function_type);
  declarator_type.add_subtype() = reference_type(uninitialized_typet{});
  to_type_with_subtype(declarator_type)
    .subtype()
    .add(ID_C_qualifier)
    .make_nil();

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

  args_decl_declor.type() = pointer_type(uninitialized_typet{});
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

  code_blockt block;

  std::string arg_name("ref");

  // First, we copy the parents
  for(const auto &b : to_struct_type(symbol.type).bases())
  {
    DATA_INVARIANT(b.id() == ID_base, "base class expression expected");

    const symbolt &symb = lookup(b.type());

    // Check that the base class's copy assignment operator is accessible
    // from the derived class.
    const struct_typet &base_struct = to_struct_type(symb.type);
    cpp_scopet *saved_scope = cpp_scopes.current_scope_ptr;
    cpp_scopes.current_scope_ptr = &cpp_scopes.get_scope(symbol.name);
    for(const auto &comp : base_struct.components())
    {
      if(
        comp.get_base_name() == "operator=" && !comp.get_bool(ID_is_static) &&
        !comp.get_bool(ID_from_base) && comp.type().id() == ID_code)
      {
        if(check_component_access(comp, base_struct))
        {
          cpp_scopes.current_scope_ptr = saved_scope;
          error().source_location = source_location;
          error() << "base class '" << symb.base_name
                  << "' has inaccessible copy assignment operator" << eom;
          throw 0;
        }
        break;
      }
    }
    cpp_scopes.current_scope_ptr = saved_scope;

    copy_parent(source_location, symb.base_name, arg_name, block);
  }

  // Then, we copy the members
  for(const auto &c : to_struct_type(symbol.type).components())
  {
    if(
      c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
      c.get_bool(ID_is_static) || c.get_bool(ID_is_vtptr) ||
      c.type().id() == ID_code)
    {
      continue;
    }

    const irep_idt &mem_name = c.get_base_name();

    if(c.type().id() == ID_array)
    {
      const exprt &size_expr = to_array_type(c.type()).size();

      if(size_expr.id()==ID_infinity)
      {
        // error().source_location=object);
        // err << "cannot copy array of infinite size\n";
        // throw 0;
        continue;
      }

      const auto size = numeric_cast<mp_integer>(size_expr);
      CHECK_RETURN(size.has_value());
      CHECK_RETURN(*size >= 0);

      for(mp_integer i = 0; i < *size; ++i)
        copy_array(source_location, mem_name, i, arg_name, block);
    }
    else
      copy_member(source_location, mem_name, arg_name, block);
  }

  // Finally we add the return statement
  block.add(
    code_returnt(dereference_exprt(exprt("cpp-this"), uninitialized_typet())));

  declarator.value() = std::move(block);
  declarator.value().add_source_location() = source_location;
}

/// Check a constructor initialization-list. An initializer has to be a data
/// member declared in this class or a direct-parent constructor. If an invalid
/// initializer is found, then the method outputs an error message and throws
/// a 0 exception.
/// \param bases: the parents of the class
/// \param components: the components of the class
/// \param initializers: the constructor initializers
/// \param class_identifier: the identifier of the class being constructed
void cpp_typecheckt::check_member_initializers(
  const struct_typet::basest &bases,
  const struct_typet::componentst &components,
  const irept &initializers,
  const irep_idt &class_identifier)
{
  PRECONDITION(initializers.id() == ID_member_initializers);

  for(const auto &initializer : initializers.get_sub())
  {
    PRECONDITION(initializer.is_not_nil());

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
      for(const auto &b : bases)
      {
        if(
          to_struct_tag_type(member_type).get_identifier() ==
          to_struct_tag_type(b.type()).get_identifier())
        {
          ok=true;
          break;
        }
      }

      if(!ok)
      {
        error().source_location=member_name.source_location();
        error() << "invalid initializer '" << member_name.to_string() << "'"
                << eom;
        throw 0;
      }
      return;
    }

    irep_idt base_name=member_name.get_base_name();
    bool ok=false;

    // First check if it matches a direct base class by name.
    // This handles the case where the base class name is not in scope
    // during template instantiation (e.g., out-of-class constructor
    // definition for a template class with a nested base class).
    for(const auto &b : bases)
    {
      if(b.type().id() != ID_struct_tag)
        continue;
      const irep_idt &base_id = to_struct_tag_type(b.type()).get_identifier();
      const symbolt &base_sym = lookup(base_id);
      if(base_sym.base_name == base_name)
      {
        ok = true;
        break;
      }
    }

    if(ok)
      continue;

    for(const auto &c : components)
    {
      if(c.get_base_name() != base_name)
        continue;

      // Data member
      if(
        !c.get_bool(ID_from_base) && !c.get_bool(ID_is_static) &&
        c.type().id() != ID_code)
      {
        ok=true;
        break;
      }

      // Maybe it is a parent constructor?
      if(c.get_bool(ID_is_type))
      {
        if(c.type().id() != ID_struct_tag)
          continue;

        const symbolt &symb =
          lookup(to_struct_tag_type(c.type()).get_identifier());
        if(symb.type.id()!=ID_struct)
          break;

        // check for a direct parent
        for(const auto &b : bases)
        {
          if(symb.name == to_struct_tag_type(b.type()).get_identifier())
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
        for(const auto &b : bases)
        {
          if(
            member_type.get(ID_identifier) ==
            to_struct_tag_type(b.type()).get_identifier())
          {
            ok=true;
            break;
          }
        }
        break;
      }

      // Delegating constructor (C++11): the initializer names the
      // class's own constructor
      if(
        !c.get_bool(ID_from_base) && !c.get_bool(ID_is_type) &&
        !c.get_bool(ID_is_static) && c.type().id() == ID_code &&
        to_code_type(c.type()).return_type().id() == ID_constructor)
      {
        ok = true;
        break;
      }
    }

    if(!ok)
    {
      // Try resolving as a type name
      typet member_type = (typet &)initializer.find(ID_member);
      try
      {
        typecheck_type(member_type);
      }
      catch(...)
      {
        member_type.make_nil();
      }

      if(member_type.id() == ID_struct_tag)
      {
        // Delegating constructor (C++11): the initializer names the
        // class's own type.
        if(
          !class_identifier.empty() &&
          to_struct_tag_type(member_type).get_identifier() == class_identifier)
        {
          ok = true;
        }

        for(const auto &b : bases)
        {
          if(
            to_struct_tag_type(member_type).get_identifier() ==
            to_struct_tag_type(b.type()).get_identifier())
          {
            ok = true;
            break;
          }
        }
      }
    }

    if(!ok)
    {
      error().source_location=member_name.source_location();
      error() << "invalid initializer '" << base_name << "'" << eom;
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
/// \param [out] initializers: the constructor initializers
void cpp_typecheckt::full_member_initialization(
  const struct_union_typet &struct_union_type,
  irept &initializers)
{
  const struct_union_typet::componentst &components=
    struct_union_type.components();

  PRECONDITION(initializers.id() == ID_member_initializers);

  // Per [temp.variadic]/7: remove empty pack expansion
  // expressions from member initializer arguments.
  if(!template_map.pack_size_map.empty())
  {
    std::set<std::string> ep_names;
    for(const auto &ps : template_map.pack_size_map)
      if(ps.second == 0)
      {
        const std::string f = id2string(ps.first);
        auto p = f.rfind("::");
        ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    if(!ep_names.empty())
    {
      std::function<bool(const irept &)> refs_empty_pack =
        [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(refs_empty_pack(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_empty_pack(ns.second))
            return true;
        return false;
      };
      for(auto &init : initializers.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return refs_empty_pack(s); }),
          subs.end());
      }
    }
  }

  // Delegating constructors (C++11) delegate to another constructor of the
  // same class. No base class or member initialization should be added.
  if(struct_union_type.id() == ID_struct)
  {
    for(const auto &initializer : initializers.get_sub())
    {
      const cpp_namet &member_name = to_cpp_name(initializer.find(ID_member));
      if(!member_name.has_template_args())
      {
        irep_idt base_name = member_name.get_base_name();
        for(const auto &c : to_struct_type(struct_union_type).components())
        {
          if(
            c.get_base_name() == base_name && !c.get_bool(ID_from_base) &&
            !c.get_bool(ID_is_type) && !c.get_bool(ID_is_static) &&
            c.type().id() == ID_code &&
            to_code_type(c.type()).return_type().id() == ID_constructor)
          {
            // The initializer names the class's own constructor.
            return;
          }
        }
      }
    }
  }

  irept final_initializers(ID_member_initializers);

  if(struct_union_type.id()==ID_struct)
  {
    // First, if we are the most-derived object, then
    // we need to construct the virtual bases
    std::list<irep_idt> vbases;
    get_virtual_bases(to_struct_type(struct_union_type), vbases);

    if(!vbases.empty())
    {
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

      code_ifthenelset cond(
        cpp_namet("@most_derived").as_expr(), std::move(block));
      final_initializers.move_to_sub(cond);
    }

    // Subsequently, we need to call the non-POD parent constructors
    for(const auto &b : to_struct_type(struct_union_type).bases())
    {
      DATA_INVARIANT(b.id() == ID_base, "base class expression expected");

      const symbolt &ctorsymb = lookup(b.type());

      if(cpp_is_pod(ctorsymb.type))
        continue;

      irep_idt ctor_name=ctorsymb.base_name;

      // Check if the initialization list of the constructor
      // explicitly calls the parent constructor.
      bool found=false;

      for(irept initializer : initializers.get_sub())
      {
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
              c.get_base_name() == base_name && c.type().id() != ID_code &&
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

        // First try matching by base class name directly — this
        // avoids type resolution failures during template instantiation
        // when the base class name is not in scope.
        {
          irep_idt init_base_name =
            to_cpp_name(initializer.find(ID_member)).get_base_name();
          if(ctorsymb.base_name == init_base_name)
          {
            final_initializers.move_to_sub(initializer);
            found = true;
            break;
          }
        }

        typecheck_type(member_type);

        if(member_type.id() != ID_struct_tag)
          break;

        if(
          to_struct_tag_type(b.type()).get_identifier() ==
          to_struct_tag_type(member_type).get_identifier())
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
        // Record the specific base subobject's type so that
        // `typecheck_member_initializer` can disambiguate among
        // base constructors that share an unqualified `base_name`
        // (e.g., a class deriving from two specializations of the
        // same template — `_Hashtable_ebo_helper<0, _Hash>` and
        // `_Hashtable_ebo_helper<1, _Equal>` — both produce
        // candidates printed as `ebo(struct ebo *)`).  The
        // resolve() call sees only the unqualified `ctor_name`
        // and would fail with "symbol 'X' does not uniquely
        // resolve" otherwise.
        mem_init.add("#base_type") = b.type();
        final_initializers.move_to_sub(mem_init);
      }

      if(b.get_bool(ID_virtual))
      {
        codet tmp(ID_member_initializer);
        tmp.swap(final_initializers.get_sub().back());

        code_ifthenelset cond(
          cpp_namet("@most_derived").as_expr(), std::move(tmp));

        final_initializers.get_sub().back().swap(cond);
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

      const symbolt *virtual_table_symbol_type;
      if(lookup(
           to_pointer_type(c.type()).base_type().get(ID_identifier),
           virtual_table_symbol_type))
        continue;

      const symbolt *virtual_table_symbol_var;
      if(lookup(
           id2string(virtual_table_symbol_type->name) + "@" +
             id2string(struct_union_type.get(ID_name)),
           virtual_table_symbol_var))
        continue;

      exprt var = virtual_table_symbol_var->symbol_expr();
      address_of_exprt address(var);
      CHECK_RETURN(address.type() == c.type());

      already_typechecked_exprt::make_already_typechecked(address);

      exprt ptrmember(ID_ptrmember);
      ptrmember.set(ID_component_name, c.get_name());
      ptrmember.operands().push_back(exprt("cpp-this"));

      code_frontend_assignt assign(ptrmember, address);
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
    for(auto &initializer : initializers.get_sub())
    {
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
    // initialized. In template classes, the default constructor
    // is implicitly deleted when a member is a reference.
    // Don't throw — just skip the default initialization.
    if(
      !found && c.type().id() == ID_pointer &&
      c.type().get_bool(ID_C_reference))
    {
      continue;
    }

    // A class/array member whose type has a default member initializer
    // (NSDMI) has a non-trivial default constructor ([class.default.ctor]/3)
    // even when it is otherwise a POD-like aggregate, so it must be
    // default-constructed for its NSDMIs to take effect.
    bool member_type_has_nsdmi = false;
    {
      typet base_type = c.type();
      while(base_type.id() == ID_array)
        base_type = to_array_type(base_type).element_type();
      if(base_type.id() == ID_struct_tag)
      {
        // [temp.inst]/2 + [class.default.ctor]/3: the member's type must be
        // complete to determine whether its default construction is
        // non-trivial (NSDMIs / a non-trivial default constructor).  A
        // class-template-instance member may still be incomplete here because
        // its elaboration was deferred -- notably the primary-template
        // fallback selected after a conditional-SFINAE partial specialization
        // was rejected (e.g. `cref<int,int*>` once
        // `void_t<decltype(false ? a : b)>` removes the specialization, the
        // libstdc++ common_reference shape).  A cleanly-matched member (e.g.
        // the partial specialization `cref<int,int>`) is already complete
        // here, so the two would otherwise be treated inconsistently and the
        // incomplete member's NSDMIs would be silently dropped from the
        // constructor.  Elaborate it first so its NSDMIs are visible; an
        // elaboration failure is non-fatal (the member is left as-is).
        try
        {
          elaborate_class_template(base_type);
        }
        catch(...)
        {
        }
        const struct_typet &member_struct =
          follow_tag(to_struct_tag_type(base_type));
        for(const auto &mc : member_struct.components())
        {
          if(
            !mc.get_bool(ID_is_static) && !mc.get_bool(ID_is_type) &&
            mc.type().id() != ID_code &&
            mc.find(ID_C_default_value).is_not_nil())
          {
            member_type_has_nsdmi = true;
            break;
          }
        }
      }
    }

    // If the data member is not POD (or has a non-trivial default
    // constructor because its type has a default member initializer) and is
    // not explicitly initialized, then its default constructor is called.
    if(!found && (!cpp_is_pod(c.type()) || member_type_has_nsdmi))
    {
      cpp_namet cppname(mem_name);

      codet mem_init(ID_member_initializer);
      mem_init.set(ID_member, cppname);
      final_initializers.move_to_sub(mem_init);
    }

    // C++11: apply default member initializer if not explicitly initialized
    if(!found && c.find(ID_C_default_value).is_not_nil())
    {
      const exprt &default_val =
        static_cast<const exprt &>(c.find(ID_C_default_value));
      cpp_namet cppname(mem_name);

      codet mem_init(ID_member_initializer);
      mem_init.set(ID_member, cppname);
      mem_init.add_to_operands(default_val);
      final_initializers.move_to_sub(mem_init);
    }
  }

  initializers.swap(final_initializers);
}

/// \par parameters: typechecked compound symbol
/// \return return true if a copy constructor is found
bool cpp_typecheckt::find_cpctor(const symbolt &symbol) const
{
  for(const auto &component : to_struct_type(symbol.type).components())
  {
    // Skip non-ctor
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

    // [class.copy] p2: A copy constructor has a first parameter of
    // type X&, const X&, volatile X&, or const volatile X&.
    // Rvalue references (X&&) are move constructors, not copy constructors.
    if(is_rvalue_reference(parameter1_type))
      continue;

    if(
      to_reference_type(parameter1_type).base_type().get(ID_identifier) !=
      symbol.name)
    {
      continue;
    }

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

    if(
      to_reference_type(arg1_type).base_type().get(ID_identifier) !=
      symbol.name)
      continue;

    return true;
  }

  return false;
}
