/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_instruction_code.h>

#include <ansi-c/anonymous_member.h>

#include "cpp_sfinae_context.h"
#include "cpp_typecheck.h"

/// Generate code to copy the parent.
/// \param source_location: location for generated code
/// \param parent_base_name: base name of typechecked parent
/// \param arg_name: name of argument that is being copied
/// \param [out] block: non-typechecked block
static void copy_parent(
  const source_locationt &source_location,
  const typet &parent_type,
  const irep_idt &arg_name,
  exprt &block,
  bool is_move = false)
{
  // N5008 [class.copy.assign]/12: each base subobject is identified by
  // its TYPE.  Build the slicing casts from the resolved base type
  // rather than the base's unqualified name: with two bases from the
  // same class template (libstdc++'s _Hashtable_base :
  // _Hashtable_ebo_helper<1,...>, _Hashtable_ebo_helper<0,...>) the
  // unqualified name does not uniquely resolve.
  typet base_t = parent_type;
  base_t.remove(ID_C_base_name);
  exprt op0("explicit-typecast", pointer_type(base_t));
  op0.copy_to_operands(exprt("cpp-this"));
  op0.add_source_location()=source_location;

  exprt op1("explicit-typecast", pointer_type(base_t));
  op1.type().set(ID_C_reference, true);
  if(is_move)
    op1.type().set(ID_C_rvalue_reference, true);
  else
    to_pointer_type(op1.type()).base_type().set(ID_C_constant, true);
  op1.get_sub().push_back(cpp_namet(arg_name, source_location));
  op1.add_source_location()=source_location;

  // [class.copy.assign]/12: the implicit move-assignment operator assigns
  // each base from the corresponding subobject of the source cast to an
  // xvalue, *as if by the base's move-assignment operator*, so its side
  // effects run (e.g. libstdc++'s __uniq_ptr_impl::operator=(&&) resets the
  // target and nulls the moved-from pointer).  Use an expression assignment,
  // which overload-resolves to the base's operator=; the copy path keeps the
  // frontend assignment (a direct subobject copy) as before.
  if(is_move)
  {
    side_effect_expr_assignt assign(
      dereference_exprt(op0), op1, typet(), source_location);
    assign.lhs().add_source_location() = source_location;
    code_expressiont code(assign);
    code.add_source_location() = source_location;
    block.operands().push_back(code);
    return;
  }

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
  exprt &block,
  bool is_move = false,
  const typet &member_type = typet{})
{
  cpp_namet op0(member_base_name, source_location);

  exprt op1(ID_member);
  op1.add(ID_component_cpp_name, cpp_namet(member_base_name, source_location));
  op1.copy_to_operands(cpp_namet(arg_name, source_location).as_expr());
  op1.add_source_location()=source_location;

  // [class.copy.assign]/12: the implicit move-assignment operator assigns
  // each member from the corresponding member of the source cast to an
  // xvalue, selecting the member's move-assignment operator (for scalars the
  // xvalue simply yields the value, coinciding with a copy).
  if(is_move && member_type.is_not_nil() && member_type.id() != ID_empty)
  {
    reference_typet rref = reference_type(member_type);
    rref.set(ID_C_rvalue_reference, true);
    exprt cast("explicit-typecast", rref);
    cast.add_source_location() = source_location;
    cast.add_to_operands(std::move(op1));
    op1 = std::move(cast);
  }

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
  // N5008 [class.default.ctor]/1, [class.copy.ctor]/6: this constructor
  // is implicitly declared, not user-declared; aggregate detection
  // ([dcl.init.aggr]/1) must ignore it.  The flag rides on the function
  // type, mirroring #is_implicit_dtor.  default_cpctor builds on this
  // declarator too, so implicit copy/move constructors inherit it.
  decl.type().set("#is_implicit_ctor", true);
  decl.add_source_location()=source_location;

  decl.value() = code_blockt();
  decl.add(ID_cv).make_nil();
  decl.add(ID_throw_decl).make_nil();

  ctor.type().id(ID_constructor);
  ctor.add(ID_storage_spec).id(ID_cpp_storage_spec);
  ctor.add_to_operands(std::move(decl));
  ctor.add_source_location()=source_location;
}

/// Generate code for implicit default copy or move constructor.
/// \param is_move: when true, generate a *move* constructor -- each base and
///   non-static data member is initialized from the corresponding subobject of
///   the argument cast to an xvalue (static_cast<T&&>), so overload resolution
///   selects the subobject's move constructor ([class.copy.ctor]/15).
void cpp_typecheckt::default_cpctor(
  const symbolt &symbol,
  cpp_declarationt &cpctor,
  const irep_idt &param_identifier_arg,
  bool is_move) const
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

  // [class.copy.ctor]/14: the implicit copy constructor of a union copies the
  // object representation.  A union has no base classes and copying it
  // member-by-member is not meaningful (at most one member is active), so emit
  // a single whole-object copy `*this = other` and return.
  if(symbol.type.id() == ID_union)
  {
    exprt op0("explicit-typecast", pointer_type(cppcomp.as_type()));
    op0.copy_to_operands(exprt("cpp-this"));
    op0.add_source_location() = source_location;

    exprt op1("explicit-typecast", pointer_type(cppcomp.as_type()));
    op1.type().set(ID_C_reference, true);
    to_pointer_type(op1.type()).base_type().set(ID_C_constant, true);
    op1.get_sub().push_back(cpp_namet(param_identifier, source_location));
    op1.add_source_location() = source_location;

    code_frontend_assignt assign_code(dereference_exprt(op0), op1);
    assign_code.add_source_location() = source_location;
    initializers.move_to_sub(assign_code);
    return;
  }

  // First, we need to call the parent copy constructors
  for(const auto &b : to_struct_type(symbol.type).bases())
  {
    DATA_INVARIANT(b.id() == ID_base, "base class expression expected");

    const symbolt &parsymb = lookup(b.type());

    if(cpp_is_pod(parsymb.type))
    {
      // For POD bases, generate a direct assignment as an initializer
      // so it runs before member copies (correct C++ init order).
      // Use the resolved base type, not the unqualified name -- see
      // copy_parent ([class.copy.ctor]/14, the _Hashtable_ebo_helper
      // double-base shape).
      typet pod_base_t = b.type();
      pod_base_t.remove(ID_C_base_name);
      exprt op0("explicit-typecast", pointer_type(pod_base_t));
      op0.copy_to_operands(exprt("cpp-this"));
      op0.add_source_location() = source_location;

      exprt op1("explicit-typecast", pointer_type(pod_base_t));
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

      // Call the parent copy/move constructor.  N5008 [class.copy.ctor]/14:
      // each base subobject is copied using its own copy constructor, applied
      // to the corresponding base subobject of the source.  Slice the source
      // parameter to a `const Base&` (rather than passing the whole derived
      // object) so overload resolution sees the base type: passing the derived
      // object would let a converting/forwarding constructor template in the
      // base (e.g. `Base(U&&)`) deduce `U` as the derived type and match more
      // closely than the base copy constructor, selecting an unintended
      // constructor ([over.match.best], [temp.deduct]).
      // For a defaulted MOVE constructor, [class.copy.ctor]/15: each base is
      // direct-initialized from the corresponding subobject of the argument
      // cast to an xvalue -- slice to `Base&&` instead, so overload resolution
      // selects the base's move constructor and its side effects run (e.g.
      // libstdc++'s __uniq_ptr_impl(__uniq_ptr_impl&&) nulls the moved-from
      // pointer).
      const cpp_namet cppname(ctor_name, source_location);

      // Build the slicing cast's target type from the resolved base type
      // (b.type(), a struct_tag) rather than the base's unqualified name: in
      // an EBO-recursive hierarchy such as std::tuple's _Tuple_impl /
      // _Head_base chain, the unqualified name is visible for several
      // distinct specializations at once and does not uniquely resolve.
      typet base_t = b.type();
      base_t.remove(ID_C_base_name);
      exprt base_ref("explicit-typecast", pointer_type(base_t));
      base_ref.type().set(ID_C_reference, true);
      if(is_move)
        base_ref.type().set(ID_C_rvalue_reference, true);
      else
        to_pointer_type(base_ref.type()).base_type().set(ID_C_constant, true);
      base_ref.get_sub().push_back(
        cpp_namet(param_identifier, source_location));
      base_ref.add_source_location() = source_location;

      codet mem_init(ID_member_initializer);
      mem_init.add_source_location()=source_location;
      mem_init.set(ID_member, cppname);
      // Record the specific base subobject's type so the initializer's
      // constructor lookup is scoped to that base (see `#base_type` in
      // typecheck_member_initializer); the unqualified base name alone is
      // ambiguous in the same hierarchies as above.
      mem_init.add("#base_type") = b.type();
      mem_init.add_to_operands(std::move(base_ref));
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
      mem_c.get_bool(ID_is_static) || mem_c.get_is_padding() ||
      mem_c.type().id() == ID_code)
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
    {
      memberexpr.set(ID_C_array_ini, true);
      mem_init.add_to_operands(std::move(memberexpr));
    }
    else if(is_move)
    {
      // [class.copy.ctor]/15: a defaulted move constructor initializes each
      // non-static data member from the corresponding member of the argument
      // cast to an xvalue.  Wrap the source access in static_cast<T&&> so that
      // overload resolution selects the member's move constructor (falling
      // back to the copy constructor when there is no viable move
      // constructor).  For a scalar member the xvalue simply yields its value,
      // so this coincides with a copy.
      reference_typet rref = reference_type(mem_c.type());
      rref.set(ID_C_rvalue_reference, true);
      exprt cast("explicit-typecast", rref);
      cast.add_source_location() = source_location;
      cast.add_to_operands(std::move(memberexpr));
      mem_init.add_to_operands(std::move(cast));
    }
    else
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
  // operator= returns a reference to the class; for a union the class type is
  // a union_tag, not a struct_tag ([class.union]).
  cpctor.type().id(symbol.type.id() == ID_union ? ID_union_tag : ID_struct_tag);
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
  cpp_declaratort &declarator,
  bool is_move)
{
  // save source location
  source_locationt source_location=declarator.source_location();
  declarator.make_nil();

  code_blockt block;

  std::string arg_name("ref");

  // [class.copy.assign]: the implicit copy-assignment operator of a union
  // copies the object representation.  A union has no bases and member-by-member
  // copy is not meaningful, so emit a single whole-object copy `*this = ref`
  // via copy_parent (a frontend assignment, not an `operator=` call, which
  // would recurse) reusing the union's own type, then return *this.
  if(symbol.type.id() == ID_union)
  {
    copy_parent(source_location, union_tag_typet{symbol.name}, arg_name, block);
    block.add(code_returnt(
      dereference_exprt(exprt("cpp-this"), uninitialized_typet())));
    declarator.value() = std::move(block);
    declarator.value().add_source_location() = source_location;
    return;
  }

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

    copy_parent(source_location, b.type(), arg_name, block, is_move);
  }

  // Then, we copy the members
  for(const auto &c : to_struct_type(symbol.type).components())
  {
    if(
      c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
      c.get_bool(ID_is_static) || c.get_bool(ID_is_vtptr) ||
      c.get_is_padding() || c.type().id() == ID_code)
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
    {
      copy_member(
        source_location, mem_name, arg_name, block, is_move, c.type());
    }
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
  const irep_idt &class_identifier,
  bool is_template_instance)
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
      // N5008 [temp.variadic]/7: drop an empty pack expansion from the base-id
      // before resolving (e.g. `_Tuple_impl<I+1, _Tail...>` with empty
      // `_Tail`); the unsubstituted pack reference would otherwise throw.
      drop_empty_pack_template_args(member_type);
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
        // N5008 [temp.inst]/2: instantiating a class template
        // specialization instantiates only the DECLARATIONS of its
        // members; a mem-initializer list belongs to a constructor's
        // DEFINITION, whose semantic checks are deferred to its own
        // instantiation ([temp.inst]/4).  A name that cannot be
        // matched here (e.g. one denoting a still-incomplete base,
        // renamedt<ssa_exprt> with ssa_exprt forward-declared) is
        // checked again -- authoritatively -- when the constructor
        // body is converted.
        if(is_template_instance)
          continue;
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

    // [class.union.anon]: a member of an anonymous union/struct member of this
    // class may be named directly in the member-initializer list.  Recognise
    // it before the type-name fallback below, which would otherwise emit a
    // (caught, but error-count-bumping) "no match" diagnostic for the name.
    if(!ok)
    {
      const namespacet ns(symbol_table);
      const struct_tag_typet class_tag{class_identifier};
      if(
        !class_identifier.empty() &&
        symbol_table.has_symbol(class_identifier) &&
        has_component_rec(class_tag, base_name, ns))
        ok = true;
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
      // See the [temp.inst]/2 note above: for a template instance the
      // authoritative check happens when the member's definition is
      // instantiated.
      if(is_template_instance)
        continue;
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
/// best-effort source location of a member-initializer irept
static source_locationt source_location_of(const irept &initializer)
{
  const irept &loc = initializer.find(ID_C_source_location);
  if(loc.is_not_nil())
    return static_cast<const source_locationt &>(loc);
  return source_locationt();
}

void cpp_typecheckt::full_member_initialization(
  const struct_union_typet &struct_union_type,
  irept &initializers)
{
  const struct_union_typet::componentst &components=
    struct_union_type.components();

  PRECONDITION(initializers.id() == ID_member_initializers);

  // N5008 [temp.variadic]/7: normalise each member-initializer's base-id by
  // dropping pack-expansion arguments over empty packs (e.g.
  // `_Tuple_impl<I+1, _Tail...>` -> `_Tuple_impl<I+1>`), in place so the
  // base-id stays clean when later moved into the final list and type-checked.
  for(auto &initializer : initializers.get_sub())
  {
    irept &member = initializer.add(ID_member);
    if(member.is_not_nil())
      drop_empty_pack_template_args(member);
  }

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
  // same class.  N5008 [class.base.init]/6: if a mem-initializer-id
  // designates the constructor's class, the constructor is a delegating
  // constructor and no base class or member initialization takes place.
  // Per [class.base.init]/2 an unqualified mem-initializer-id is looked up
  // in the scope of the constructor's class, where a name equal to the
  // class's own name finds the injected-class-name ([class.pre]) -- i.e.
  // the class itself.  Compare against the class's name directly: scanning
  // the class's components for an already-declared constructor (as done
  // previously) made recognition declaration-order dependent, because a
  // delegating constructor declared before its target sees no constructor
  // component yet.  (A non-static data member cannot share the name of its
  // class, [class.mem.general], so a matching simple name can only mean
  // delegation.)
  if(struct_union_type.id() == ID_struct)
  {
    // The tag is qualified for nested classes ("outer::inner") and may
    // carry template arguments for class template specializations
    // ("S<tag-T>"); the injected-class-name is the plain final component
    // ([class.pre]).  The component boundary is the last "::" OUTSIDE
    // angle brackets -- a naive rfind("::") could land inside a template
    // argument.
    std::string class_base_name = id2string(struct_union_type.get(ID_tag));
    {
      std::size_t depth = 0;
      std::size_t final_component = 0;
      for(std::size_t i = 0; i + 1 < class_base_name.size(); ++i)
      {
        if(class_base_name[i] == '<')
          ++depth;
        else if(class_base_name[i] == '>' && depth > 0)
          --depth;
        else if(
          depth == 0 && class_base_name[i] == ':' &&
          class_base_name[i + 1] == ':')
        {
          final_component = i + 2;
        }
      }
      class_base_name.erase(0, final_component);
      const std::size_t angle = class_base_name.find('<');
      if(angle != std::string::npos)
        class_base_name.erase(angle);
    }
    for(const auto &initializer : initializers.get_sub())
    {
      const cpp_namet &member_name = to_cpp_name(initializer.find(ID_member));
      if(
        member_name.is_simple_name() && !class_base_name.empty() &&
        id2string(member_name.get_base_name()) == class_base_name)
      {
        // The initializer designates the constructor's class: delegating.
        return;
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
      {
        // N5008 [class.default.ctor]/3 + [class.base.init]/9.1: a default
        // member initializer makes a class's default constructor
        // non-trivial, and a base subobject not named in the
        // mem-initializer-list is initialized by that constructor -- its
        // NSDMIs must take effect.  CBMC's cpp_is_pod does not consider
        // NSDMIs, so no constructor was synthesized for such a base and
        // the skip below silently dropped its initializers (a
        // default-constructed derived object had nondet members; the
        // std::optional _Optional_payload_base::_M_engaged shape).  Apply
        // the base's initializers here, through the flattened `from_base`
        // components, mirroring the member NSDMI branches below: a
        // component with its own #default_value is initialized from it,
        // and a component whose TYPE transitively carries NSDMIs is
        // default-constructed (cpp_constructor applies them recursively).
        // Only for a base not named in the mem-initializer-list, and only
        // for non-virtual bases (the @most_derived machinery is for
        // constructor-called bases).
        if(has_default_member_initializer(b.type()) && !b.get_bool(ID_virtual))
        {
          // N5008 [dcl.init]/8: an EXPLICIT empty initializer for the base
          // (`D() : B() {}` / `: B{}`) value-initializes it, which -- the
          // default constructor being non-trivial because of the NSDMI --
          // also applies the default member initializers.  Only an
          // initializer WITH arguments (copy-initialization from another
          // object) supersedes them.
          bool named = false;
          for(const irept &initializer : initializers.get_sub())
          {
            if(initializer.find(ID_member).id() != ID_cpp_name)
              continue;
            if(
              to_cpp_name(initializer.find(ID_member)).get_base_name() ==
                ctorsymb.base_name &&
              static_cast<const exprt &>(initializer).has_operands())
            {
              named = true;
              break;
            }
          }
          if(!named)
          {
            // members of this base are the flattened components whose
            // qualified name starts with the base's member prefix: the
            // class symbol name with the "tag-" of its FINAL path
            // component removed ("ns::tag-B<tag-A>" -> "ns::B<tag-A>::").
            // The final component boundary is the last "::" OUTSIDE angle
            // brackets -- a naive rfind("tag-") would strip a template
            // ARGUMENT's tag instead (e.g. the tag-S in tag-base_<tag-S>),
            // mismatching every component.
            std::string prefix = id2string(ctorsymb.name);
            {
              std::size_t depth = 0;
              std::size_t final_component = 0;
              for(std::size_t i = 0; i + 1 < prefix.size(); ++i)
              {
                if(prefix[i] == '<')
                  ++depth;
                else if(prefix[i] == '>' && depth > 0)
                  --depth;
                else if(depth == 0 && prefix[i] == ':' && prefix[i + 1] == ':')
                  final_component = i + 2;
              }
              if(prefix.compare(final_component, 4, "tag-") == 0)
                prefix.erase(final_component, 4);
            }
            prefix += "::";
            for(const auto &c : components)
            {
              if(
                !c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
                c.get_bool(ID_is_static) || c.type().id() == ID_code ||
                c.get_is_padding())
              {
                continue;
              }
              if(id2string(c.get_name()).compare(0, prefix.size(), prefix) != 0)
                continue;
              const irept &default_val = c.find(ID_C_default_value);
              if(default_val.is_not_nil())
              {
                codet mem_init(ID_member_initializer);
                mem_init.set(ID_member, cpp_namet(c.get_base_name()));
                mem_init.copy_to_operands(
                  static_cast<const exprt &>(default_val));
                final_initializers.move_to_sub(mem_init);
              }
              else if(has_default_member_initializer(c.type()))
              {
                codet mem_init(ID_member_initializer);
                mem_init.set(ID_member, cpp_namet(c.get_base_name()));
                final_initializers.move_to_sub(mem_init);
              }
            }
          }
        }

        // N5008 [class.base.init]/7: a mem-initializer WITH an
        // expression-list initializes the (POD) base subobject from it
        // -- `wrapt(payloadt v) : payloadt(v)` copy-initializes the
        // base.  This branch previously dropped such initializers
        // silently (the base stayed nondeterministic; wrong code).  The
        // mem-initializer-id may also name the base via a TEMPLATE
        // PARAMETER ([class.base.init]/2: any name denoting the type,
        // goto-symex/renamed.h's `renamedt(underlyingt v) :
        // underlyingt(v)`), so match by name first and by resolved type
        // second.  Lower to an assignment through the sliced base
        // lvalue, the same shape copy_parent emits.
        for(const irept &initializer : initializers.get_sub())
        {
          if(initializer.find(ID_member).id() != ID_cpp_name)
            continue;
          const cpp_namet &init_name = to_cpp_name(initializer.find(ID_member));
          const exprt &init_expr = static_cast<const exprt &>(initializer);
          if(init_expr.operands().empty())
            continue;
          bool names_this_base =
            !init_name.has_template_args() &&
            init_name.get_base_name() == ctorsymb.base_name;
          if(!names_this_base)
          {
            // resolved-type match (template parameter or typedef).  Skip
            // names of data members outright, and suppress diagnostics
            // and the error count for the probe: an initializer naming a
            // MEMBER must not surface a bogus "found no match" from this
            // speculative type resolution.
            bool is_member_name = false;
            for(const auto &c : components)
            {
              if(
                c.get_base_name() == init_name.get_base_name() &&
                c.type().id() != ID_code && !c.get_bool(ID_is_type))
              {
                is_member_name = true;
                break;
              }
            }
            if(!is_member_name)
            {
              // N5008 [temp.names]/8: within the instance, a template
              // parameter denotes its bound argument -- consult the
              // active template map FIRST (scope-based resolution of
              // the parameter fails when the class is completed from a
              // re-elaboration context, [temp.point]).
              const std::string want = id2string(init_name.get_base_name());
              for(const auto &te : template_map.type_map)
              {
                const std::string key = id2string(te.first);
                const auto pos = key.rfind("::");
                if(
                  (pos != std::string::npos ? key.substr(pos + 2) : key) ==
                    want &&
                  te.second.id() == ID_struct_tag &&
                  to_struct_tag_type(te.second).get_identifier() ==
                    to_struct_tag_type(b.type()).get_identifier())
                {
                  names_this_base = true;
                  break;
                }
              }
            }
            if(!is_member_name && !names_this_base)
            {
              const std::size_t errors_before =
                get_message_handler().get_message_count(messaget::M_ERROR);
              try
              {
                sfinae_contextt sfinae_guard{*this};
                typet named_type =
                  static_cast<const typet &>(initializer.find(ID_member));
                typecheck_type(named_type);
                names_this_base =
                  named_type.id() == ID_struct_tag &&
                  to_struct_tag_type(named_type).get_identifier() ==
                    to_struct_tag_type(b.type()).get_identifier();
              }
              catch(...)
              {
                // not a type
              }
              get_message_handler().set_message_count(
                messaget::M_ERROR, errors_before);
            }
          }
          if(!names_this_base)
            continue;

          typet base_t = b.type();
          base_t.remove(ID_C_base_name);
          exprt lhs_ptr("explicit-typecast", pointer_type(base_t));
          lhs_ptr.copy_to_operands(exprt("cpp-this"));
          lhs_ptr.add_source_location() = source_location_of(initializer);
          dereference_exprt lhs(lhs_ptr);
          // N5008 [class.base.init]/7: the expression-list or braced-init-
          // list initializes the base subobject, which for an aggregate can
          // be MEMBER-WISE (`Derived() : Base{42}` with `struct Base
          // { int x; }`, [dcl.init.list]/3.4 / [dcl.init.aggr]) -- only a
          // single operand of the base's own type is a whole-object copy.
          // Assigning the bare operand mis-typechecked the aggregate form
          // ("invalid implicit conversion from 'signed int' to 'struct
          // Base'"), and a multi-operand list was dropped altogether (the
          // size()!=1 guard above; nondet base).  Route the operands
          // through an explicit-constructor-call expression instead: its
          // typecheck performs copy-initialization for the same-type form
          // and aggregate initialization otherwise.
          exprt rhs("explicit-constructor-call", base_t);
          rhs.add_source_location() = source_location_of(initializer);
          exprt init_list(ID_initializer_list);
          init_list.operands() = init_expr.operands();
          init_list.add_source_location() = source_location_of(initializer);
          rhs.add_to_operands(std::move(init_list));
          code_frontend_assignt assign_code(std::move(lhs), std::move(rhs));
          assign_code.add_source_location() = source_location_of(initializer);
          final_initializers.move_to_sub(assign_code);
          break;
        }
        continue;
      }

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

          // [class.union.anon]: a member of an anonymous union/struct member
          // is a member of this class, so an initializer naming one is a data
          // initializer (not a base-class initializer) -- do not try to
          // type-check the name as a base-class type below.
          if(!is_data)
          {
            const namespacet ns(symbol_table);
            for(const auto &c : components)
            {
              if(
                c.get_anonymous() &&
                (c.type().id() == ID_union_tag ||
                 c.type().id() == ID_struct_tag) &&
                has_component_rec(c.type(), base_name, ns))
              {
                is_data = true;
                break;
              }
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

        drop_empty_pack_template_args(member_type);

        // N5008 [temp.names]/8 + [class.base.init]/2: the
        // mem-initializer-id may denote the base via a TEMPLATE
        // PARAMETER; within the instance that parameter denotes its
        // bound argument.  Consult the active template map first --
        // scope-based resolution of the parameter fails when the class
        // is completed from a re-elaboration context ([temp.point]).
        if(!member_name.is_qualified() && !has_template_args)
        {
          const std::string want = id2string(member_name.get_base_name());
          bool matched_via_map = false;
          for(const auto &te : template_map.type_map)
          {
            const std::string key = id2string(te.first);
            const auto pos = key.rfind("::");
            if(
              (pos != std::string::npos ? key.substr(pos + 2) : key) == want &&
              te.second.id() == ID_struct_tag &&
              to_struct_tag_type(te.second).get_identifier() ==
                to_struct_tag_type(b.type()).get_identifier())
            {
              matched_via_map = true;
              break;
            }
          }
          if(matched_via_map)
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
      c.get_bool(ID_is_type) || c.get_bool(ID_is_static) || c.get_is_padding())
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

      // [class.union.anon]: an initializer naming a member of this anonymous
      // union/struct component initializes that subobject; route it to the
      // body (typecheck_member_initializer builds the access through the
      // unnamed subobject).
      if(
        c.get_anonymous() &&
        (c.type().id() == ID_union_tag || c.type().id() == ID_struct_tag))
      {
        const namespacet ns(symbol_table);
        if(has_component_rec(c.type(), base_name, ns))
        {
          final_initializers.move_to_sub(initializer);
          found = true;
          break;
        }
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
    //
    // N5008 [class.base.init]/9: a non-static data member that has a default
    // member initializer and is not named by a mem-initializer-id is
    // initialized *from that default member initializer*, not
    // default-constructed.  Such a member is handled by the block below (which
    // forwards the initializer to the member's constructor), so it must be
    // excluded here -- otherwise a class-typed member with a braced default
    // member initializer but no default constructor (e.g. `pair stored{-1, 7}`
    // where `pair` has only `pair(int, int)`) would additionally get a
    // default-construction member-initializer and fail with "found no match".
    if(
      !found && (!cpp_is_pod(c.type()) || member_type_has_nsdmi) &&
      c.find(ID_C_default_value).is_nil())
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
  for(const auto &component : to_struct_union_type(symbol.type).components())
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
  const struct_union_typet &struct_type = to_struct_union_type(symbol.type);
  const struct_union_typet::componentst &components = struct_type.components();

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
