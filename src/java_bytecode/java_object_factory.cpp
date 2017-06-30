/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_object_factory.h"

#include <unordered_set>
#include <sstream>

#include <util/arith_tools.h>
#include <util/fresh_symbol.h>
#include <util/c_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/namespace.h>
#include <util/nondet_bool.h>
#include <util/nondet_ifthenelse.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/invariant.h>

#include <linking/zero_initializer.h>

#include <goto-programs/goto_functions.h>


#include <java_bytecode/select_pointer_type.h>
#include "java_types.h"
#include "java_utils.h"

static symbolt &new_tmp_symbol(
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  const typet &type,
  const std::string &prefix="tmp_object_factory")
{
  return get_fresh_aux_symbol(
    type,
    "",
    prefix,
    loc,
    ID_java,
    symbol_table);
}

class java_object_factoryt
{
protected:
  std::vector<const symbolt *> &symbols_created;
  const source_locationt &loc;
  std::unordered_set<irep_idt, irep_id_hash> recursion_set;
  bool assume_non_null;
  size_t max_nondet_array_length;
  symbol_tablet &symbol_table;
  namespacet ns;

  void set_null(
    const exprt &expr,
    const pointer_typet &ptr_type);


  code_assignt get_null_assignment(
    const exprt &expr,
    const pointer_typet &ptr_type);

  void gen_pointer_target_init(
    code_blockt &assignments,
    const exprt &expr,
    const typet &target_type,
    bool create_dynamic_objects,
    update_in_placet update_in_place);

  void allocate_nondet_length_array(
    code_blockt &assignments,
    const exprt &lhs,
    const exprt &max_length_expr,
    const typet &element_type);

public:
  java_object_factoryt(
    std::vector<const symbolt *> &_symbols_created,
    const source_locationt &loc,
    bool _assume_non_null,
    size_t _max_nondet_array_length,
    symbol_tablet &_symbol_table):
      symbols_created(_symbols_created),
      loc(loc),
      assume_non_null(_assume_non_null),
      max_nondet_array_length(_max_nondet_array_length),
      symbol_table(_symbol_table),
      ns(_symbol_table)
  {}

  virtual ~java_object_factoryt()=default;

  exprt allocate_object(
    code_blockt &assignments,
    const exprt &,
    const typet &,
    bool create_dynamic_objects);

  void gen_nondet_array_init(
    code_blockt &assignments,
    const exprt &expr,
    update_in_placet);

  virtual void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    bool is_sub,
    irep_idt class_identifier,
    bool skip_classid,
    bool create_dynamic_objects,
    bool override,
    const typet &override_type,
    update_in_placet);

private:
  void gen_nondet_pointer_init(
    code_blockt &assignments,
    const exprt &expr,
    const irep_idt &class_identifier,
    bool create_dynamic_objects,
    const pointer_typet &pointer_type,
    const update_in_placet &update_in_place);

  void gen_nondet_struct_init(
    code_blockt &assignments,
    const exprt &expr,
    bool is_sub,
    irep_idt class_identifier,
    bool skip_classid,
    bool create_dynamic_objects,
    const struct_typet &struct_type,
    const update_in_placet &update_in_place);
};

/// Generates code for allocating a dynamic object. This is used in
/// allocate_object and for allocating strings in the library preprocessing.
/// \param target_expr: expression to which the necessary memory will be
///   allocated
/// \param allocate_type: type of the object allocated
/// \param symbol_table: symbol table
/// \param loc: location in the source
/// \param output_code: code block to which the necessary code is added
/// \param symbols_created: created symbols to be declared by the caller
/// \param cast_needed: Boolean flags saying where we need to cast the malloc
///   site
/// \return Expression representing the malloc site allocated.
exprt allocate_dynamic_object(
  const exprt &target_expr,
  const typet &allocate_type,
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  code_blockt &output_code,
  std::vector<const symbolt *> &symbols_created,
  bool cast_needed)
{
  // build size expression
  exprt object_size=size_of_expr(allocate_type, namespacet(symbol_table));

  if(allocate_type.id()!=ID_empty)
  {
    assert(!object_size.is_nil() && "size of Java objects should be known");
    // malloc expression
    exprt malloc_expr=side_effect_exprt(ID_malloc);
    malloc_expr.copy_to_operands(object_size);
    typet result_type=pointer_typet(allocate_type);
    malloc_expr.type()=result_type;
    // Create a symbol for the malloc expression so we can initialize
    // without having to do it potentially through a double-deref, which
    // breaks the to-SSA phase.
    symbolt &malloc_sym=new_tmp_symbol(
      symbol_table,
      loc,
      pointer_typet(allocate_type),
      "malloc_site");
    symbols_created.push_back(&malloc_sym);
    code_assignt assign=code_assignt(malloc_sym.symbol_expr(), malloc_expr);
    assign.add_source_location()=loc;
    output_code.copy_to_operands(assign);
    malloc_expr=malloc_sym.symbol_expr();
    if(cast_needed)
      malloc_expr=typecast_exprt(malloc_expr, target_expr.type());
    code_assignt code(target_expr, malloc_expr);
    code.add_source_location()=loc;
    output_code.copy_to_operands(code);
    return malloc_sym.symbol_expr();
  }
  else
  {
    // make null
    null_pointer_exprt null_pointer_expr(to_pointer_type(target_expr.type()));
    code_assignt code(target_expr, null_pointer_expr);
    code.add_source_location()=loc;
    output_code.copy_to_operands(code);
    return exprt();
  }
}

/// Generates code for allocating a dynamic object. This is a static version of
/// allocate_dynamic_object that can be called from outside java_object_factory
/// and which takes care of creating the associated declarations.
/// \param target_expr: expression to which the necessary memory will be
///   allocated
/// \param allocate_type: type of the object allocated
/// \param symbol_table: symbol table
/// \param loc: location in the source
/// \param output_code: code block to which the necessary code is added
/// \param cast_needed: Boolean flags saying where we need to cast the malloc
///   site
/// \return Expression representing the malloc site allocated.
exprt allocate_dynamic_object_with_decl(
  const exprt &target_expr,
  const typet &allocate_type,
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  code_blockt &output_code,
  bool cast_needed)
{
  std::vector<const symbolt *> symbols_created;

  code_blockt tmp_block;
  exprt result=allocate_dynamic_object(
    target_expr,
    allocate_type,
    symbol_table,
    loc,
    tmp_block,
    symbols_created,
    cast_needed);

  // Add the following code to output_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt * const symbol_ptr : symbols_created)
  {
    code_declt decl(symbol_ptr->symbol_expr());
    decl.add_source_location()=loc;
    output_code.add(decl);
  }

  for(const exprt &code : tmp_block.operands())
    output_code.add(to_code(code));

  return result;
}

/// Returns false if we can't figure out the size of allocate_type.
/// allocate_type may differ from target_expr, e.g. for target_expr having type
/// int* and allocate_type being an int[10].
/// \param assignments: The code block to add code to
/// \param target_expr: The expression which we are allocating a symbol for
/// \param allocate_type:
/// \param create_dynamic_objects: Whether to create a symbol with static
///   lifetime or
exprt java_object_factoryt::allocate_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  bool create_dynamic_objects)
{
  const typet &allocate_type_resolved=ns.follow(allocate_type);
  const typet &target_type=ns.follow(target_expr.type().subtype());
  bool cast_needed=allocate_type_resolved!=target_type;
  if(!create_dynamic_objects)
  {
    symbolt &aux_symbol=new_tmp_symbol(symbol_table, loc, allocate_type);
    symbols_created.push_back(&aux_symbol);

    exprt object=aux_symbol.symbol_expr();
    exprt aoe=address_of_exprt(object);
    if(cast_needed)
      aoe=typecast_exprt(aoe, target_expr.type());
    code_assignt code(target_expr, aoe);
    code.add_source_location()=loc;
    assignments.copy_to_operands(code);
    return aoe;
  }
  else
  {
    // build size expression
    exprt object_size=size_of_expr(allocate_type, namespacet(symbol_table));

    if(allocate_type.id()!=ID_empty)
    {
      assert(!object_size.is_nil() && "size of Java objects should be known");
      // malloc expression
      exprt malloc_expr=side_effect_exprt(ID_malloc);
      malloc_expr.copy_to_operands(object_size);
      typet result_type=pointer_type(allocate_type);
      malloc_expr.type()=result_type;
      // Create a symbol for the malloc expression so we can initialize
      // without having to do it potentially through a double-deref, which
      // breaks the to-SSA phase.
      symbolt &malloc_sym=new_tmp_symbol(
        symbol_table,
        loc,
        pointer_type(allocate_type),
        "malloc_site");
      symbols_created.push_back(&malloc_sym);
      code_assignt assign=code_assignt(malloc_sym.symbol_expr(), malloc_expr);
      code_assignt &malloc_assign=assign;
      malloc_assign.add_source_location()=loc;
      assignments.copy_to_operands(malloc_assign);
      malloc_expr=malloc_sym.symbol_expr();
      if(cast_needed)
        malloc_expr=typecast_exprt(malloc_expr, target_expr.type());
      code_assignt code(target_expr, malloc_expr);
      code.add_source_location()=loc;
      assignments.copy_to_operands(code);
      return malloc_sym.symbol_expr();
    }
    else
    {
      // make null
      null_pointer_exprt null_pointer_expr(to_pointer_type(target_expr.type()));
      code_assignt code(target_expr, null_pointer_expr);
      code.add_source_location()=loc;
      assignments.copy_to_operands(code);
      return exprt();
    }
  }
}

/// Adds an instruction to `init_code` null-initialising `expr`.
/// \par parameters: `expr`: pointer-typed lvalue expression to initialise
/// `ptr_type`: pointer type to write
code_assignt java_object_factoryt::get_null_assignment(
  const exprt &expr,
  const pointer_typet &ptr_type)
{
  null_pointer_exprt null_pointer_expr(ptr_type);
  code_assignt code(expr, null_pointer_expr);
  code.add_source_location()=loc;
  return code;
}

/// Initialises an object tree rooted at `expr`, allocating child objects as
/// necessary and nondet-initialising their members, or if MUST_UPDATE_IN_PLACE
/// is set, re-initialising already-allocated objects.
/// \par parameters: `expr`: pointer-typed lvalue expression to initialise
/// `target_type`: structure type to initialise, which may not match *expr (for
///   example, expr might be void*)
/// `create_dynamic_objects`: if true, use malloc to allocate objects; otherwise
///   generate fresh static symbols.
/// `update_in_place`: NO_UPDATE_IN_PLACE: initialise `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialise an existing object MAY_UPDATE_IN_PLACE:
///   invalid input
void java_object_factoryt::gen_pointer_target_init(
  code_blockt &assignments,
  const exprt &expr,
  const typet &target_type,
  bool create_dynamic_objects,
  update_in_placet update_in_place)
{
  assert(update_in_place!=MAY_UPDATE_IN_PLACE);

  if(target_type.id()==ID_struct &&
     has_prefix(
       id2string(to_struct_type(target_type).get_tag()),
       "java::array["))
  {
    gen_nondet_array_init(
      assignments,
      expr,
      update_in_place);
  }
  else
  {
    exprt target;
    if(update_in_place==NO_UPDATE_IN_PLACE)
    {
      target=allocate_object(
        assignments,
        expr,
        target_type,
        create_dynamic_objects);
    }
    else
    {
      target=expr;
    }
    exprt init_expr;
    if(target.id()==ID_address_of)
      init_expr=target.op0();
    else
    {
      init_expr=
        dereference_exprt(target, target.type().subtype());
    }
    gen_nondet_init(
      assignments,
      init_expr,
      false,
      "",
      false,
      create_dynamic_objects,
      false,
      typet(),
      update_in_place);
  }
}

/// Initialises a primitive or object tree rooted at `expr`, of type pointer. It
/// allocates child objects as necessary and nondet-initialising their members,
/// or if MUST_UPDATE_IN_PLACE is set, re-initialising already-allocated
/// objects.
/// \param assignemnts - the code block we are building with
///   initilisation code
/// \param expr: lvalue expression to initialise
/// \param class_identifier - the name of the class so we can identify
/// special cases where a null pointer is not applicable.
/// \param create_dynamic_objects: if true, use malloc to allocate objects;
///   otherwise generate fresh static symbols.
/// \param pointer_type - The type of the pointer we are initalising
/// `update_in_place`: NO_UPDATE_IN_PLACE: initialise `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialise an existing object MAY_UPDATE_IN_PLACE:
///   generate a runtime nondet branch between the NO_ and MUST_ cases.
void java_object_factoryt::gen_nondet_pointer_init(
  code_blockt &assignments,
  const exprt &expr,
  const irep_idt &class_identifier,
  bool create_dynamic_objects,
  const pointer_typet &pointer_type,
  const update_in_placet &update_in_place)
{
  const typet &subtype=ns.follow(pointer_type.subtype());
  if(subtype.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(subtype);
    const irep_idt &struct_tag=struct_type.get_tag();

    // If this is a recursive type of some kind, set null.
    if(!recursion_set.insert(struct_tag).second)
    {
      if(update_in_place==NO_UPDATE_IN_PLACE)
      {
        assignments.copy_to_operands(
          get_null_assignment(expr, pointer_type));
      }
      // Otherwise leave it as it is.
      return;
    }
  }

  code_blockt new_object_assignments;
  code_blockt update_in_place_assignments;

  if(update_in_place!=NO_UPDATE_IN_PLACE)
  {
    gen_pointer_target_init(
      update_in_place_assignments,
      expr,
      subtype,
      create_dynamic_objects,
      MUST_UPDATE_IN_PLACE);
  }

  if(update_in_place==MUST_UPDATE_IN_PLACE)
  {
    assignments.append(update_in_place_assignments);
    return;
  }

  // Otherwise we need code for the allocate-new-object case:

  code_blockt non_null_inst;
  gen_pointer_target_init(
    non_null_inst,
    expr,
    subtype,
    create_dynamic_objects,
    NO_UPDATE_IN_PLACE);

  // Determine whether the pointer can be null.
  // In particular the array field of a String should not be null.
  bool not_null=
    assume_non_null ||
    ((class_identifier=="java.lang.String" ||
      class_identifier=="java.lang.StringBuilder" ||
      class_identifier=="java.lang.StringBuffer" ||
      class_identifier=="java.lang.CharSequence") &&
     subtype.id()==ID_array);

  if(not_null)
  {
    // Add the following code to assignments:
    // <expr> = <aoe>;
    new_object_assignments.append(non_null_inst);
  }
  else
  {
    // if(NONDET(_Bool)
    // {
    //    <expr> = <null pointer>
    // }
    // else
    // {
    //    <code from recursive call to gen_nondet_init() with
    //             tmp$<temporary_counter>>
    // }
    auto set_null_inst=get_null_assignment(expr, pointer_type);

    code_ifthenelset null_check;
    null_check.cond()=side_effect_expr_nondett(bool_typet());
    null_check.then_case()=set_null_inst;
    null_check.else_case()=non_null_inst;

    new_object_assignments.add(null_check);
  }

  // Similarly to above, maybe use a conditional if both the
  // allocate-fresh and update-in-place cases are allowed:
  if(update_in_place==NO_UPDATE_IN_PLACE)
  {
    assignments.append(new_object_assignments);
  }
  else
  {
    INVARIANT(update_in_place==MAY_UPDATE_IN_PLACE,
      "No update and must update should have already been resolved");

    code_ifthenelset update_check;
    update_check.cond()=side_effect_expr_nondett(bool_typet());
    update_check.then_case()=update_in_place_assignments;
    update_check.else_case()=new_object_assignments;

    assignments.add(update_check);
  }
}

/// Initialises an object tree rooted at `expr`, allocating child objects as
/// necessary and nondet-initialising their members, or if MUST_UPDATE_IN_PLACE
/// is set, re-initialising already-allocated objects.
/// \param assignments: The code block to append the new
///   instructions to
/// \param expr: pointer-typed lvalue expression to initialise
/// \param is_sub: If true, `expr` is a substructure of a larger object, which
///   in Java necessarily means a base class. not match *expr (for example, expr
///   might be void*)
/// \param class_identifier: clsid to initialise @java.lang.Object.
///   @class_identifier
/// \param skip_classid: if true, skip initialising @class_identifier
/// \param create_dynamic_objects: if true, use malloc to allocate objects;
///   otherwise generate fresh static symbols.
/// \param struct_type - The type of the struct we are initalising
/// \param update_in_place: NO_UPDATE_IN_PLACE: initialise `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialise an existing object MAY_UPDATE_IN_PLACE:
///   invalid input
void java_object_factoryt::gen_nondet_struct_init(
  code_blockt &assignments,
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  bool create_dynamic_objects,
  const struct_typet &struct_type,
  const update_in_placet &update_in_place)
{
  typedef struct_typet::componentst componentst;
  const irep_idt &struct_tag=struct_type.get_tag();

  const componentst &components=struct_type.components();

  if(!is_sub)
    class_identifier=struct_tag;

  for(const auto &component : components)
  {
    const typet &component_type=component.type();
    irep_idt name=component.get_name();

    member_exprt me(expr, name, component_type);

    if(name=="@class_identifier")
    {
      if(update_in_place==MUST_UPDATE_IN_PLACE)
        continue;

      if(skip_classid)
        continue;

      irep_idt qualified_clsid="java::"+as_string(class_identifier);
      constant_exprt ci(qualified_clsid, string_typet());
      code_assignt code(me, ci);
      code.add_source_location()=loc;
      assignments.copy_to_operands(code);
    }
    else if(name=="@lock")
    {
      if(update_in_place==MUST_UPDATE_IN_PLACE)
        continue;
      code_assignt code(me, from_integer(0, me.type()));
      code.add_source_location()=loc;
      assignments.copy_to_operands(code);
    }
    else
    {
      INVARIANT(!name.empty(), "Each component of a struct must have a name");

      bool _is_sub=name[0]=='@';

      // MUST_UPDATE_IN_PLACE only applies to this object.
      // If this is a pointer to another object, offer the chance
      // to leave it alone by setting MAY_UPDATE_IN_PLACE instead.
      update_in_placet substruct_in_place=
        update_in_place==MUST_UPDATE_IN_PLACE && !_is_sub ?
        MAY_UPDATE_IN_PLACE :
        update_in_place;
      gen_nondet_init(
        assignments,
        me,
        _is_sub,
        class_identifier,
        false,
        create_dynamic_objects,
        false,
        typet(),
        substruct_in_place);
    }
  }
}

/// Initialises a primitive or object tree rooted at `expr`, allocating child
/// objects as necessary and nondet-initialising their members, or if
/// MUST_UPDATE_IN_PLACE is set, re-initialising already-allocated objects.
/// \par parameters: `expr`: lvalue expression to initialise
/// `is_sub`: If true, `expr` is a substructure of a larger object, which in
///   Java necessarily means a base class. not match *expr (for example, expr
///   might be void*)
/// \param class_identifier: clsid to initialise @java.lang.Object.
///   @class_identifier
/// \param create_dynamic_objects: if true, use malloc to allocate objects;
///   otherwise generate fresh static symbols.
/// \param struct_type - The type of the struct we are initalising
void java_object_factoryt::gen_nondet_struct_init(
  code_blockt &assignments,
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  bool create_dynamic_objects,
  const struct_typet &struct_type)
{
  typedef struct_typet::componentst componentst;

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    gen_nondet_pointer_init(
      assignments,
      expr,
      class_identifier,
      create_dynamic_objects,
      NO_UPDATE_IN_PLACE);

    // Determine whether the pointer can be null.
    // In particular the array field of a String should not be null.
    bool not_null=
      assume_non_null ||
      ((class_identifier=="java.lang.String" ||
        class_identifier=="java.lang.StringBuilder" ||
        class_identifier=="java.lang.StringBuffer" ||
        class_identifier=="java.lang.CharSequence") &&
       subtype.id()==ID_array);

    if(not_null)
    {
      // Add the following code to assignments:
      // <expr> = <aoe>;
      new_object_assignments.append(non_null_inst);
    }
    else
    {
      // Add the following code to assignments:
      //           IF !NONDET(_Bool) THEN GOTO <label1>
      //           <expr> = <null pointer>
      //           GOTO <label2>
      // <label1>: <expr> = &tmp$<temporary_counter>;
      //           <code from recursive call to gen_nondet_init() with
      //             tmp$<temporary_counter>>
      // And the next line is labelled label2
      auto set_null_inst=get_null_assignment(expr, pointer_type);

      code_ifthenelset null_check;
      null_check.cond()=side_effect_expr_nondett(bool_typet());
      null_check.then_case()=set_null_inst;
      null_check.else_case()=non_null_inst;

      new_object_assignments.add(null_check);
    }

    if(update_in_place==MAY_UPDATE_IN_PLACE)
      update_in_place_diamond.finish();
  }
}

/// Initialises a primitive or object tree rooted at `expr`, allocating child
/// objects as necessary and nondet-initialising their members, or if
/// MUST_UPDATE_IN_PLACE is set, re-initialising already-allocated objects.
/// \par parameters: `expr`: lvalue expression to initialise
/// `is_sub`: If true, `expr` is a substructure of a larger object, which in
///   Java necessarily means a base class. not match *expr (for example, expr
///   might be void*)
/// `class_identifier`: clsid to initialise @java.lang.Object. @class_identifier
/// `skip_classid`: if true, skip initialising @class_identifier
/// `create_dynamic_objects`: if true, use malloc to allocate objects; otherwise
///   generate fresh static symbols.
/// `override`: If true, initialise with `override_type` instead of
///   `expr.type()`. Used at the moment for reference arrays, which are
///   implemented as void* arrays but should be init'd as their true type with
///   appropriate casts.
/// `override_type`: Override type per above
/// `update_in_place`: NO_UPDATE_IN_PLACE: initialise `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialise an existing object MAY_UPDATE_IN_PLACE:
///   generate a runtime nondet branch between the NO_ and MUST_ cases.
void java_object_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  bool create_dynamic_objects,
  bool override,
  const typet &override_type,
  update_in_placet update_in_place)
{
  const typet &type=
    override ? ns.follow(override_type) : ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    gen_nondet_pointer_init(
      assignments,
      expr,
      class_identifier,
      create_dynamic_objects,
      pointer_type,
      update_in_place);
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet struct_type=to_struct_type(type);
    gen_nondet_struct_init(
      assignments,
      expr,
      is_sub,
      class_identifier,
      skip_classid,
      create_dynamic_objects,
      struct_type,
      update_in_place);
  }
  else
  {
    exprt rhs=type.id()==ID_c_bool?
      get_nondet_bool(type):
      side_effect_expr_nondett(type);
    code_assignt assign(expr, rhs);
    assign.add_source_location()=loc;

    assignments.copy_to_operands(assign);
  }
}

/// Allocates a fresh array. Single-use at the moment, but useful to keep
/// as a separate function for downstream branches.
/// \par parameters: `lhs`, symbol to assign the new array structure
/// `max_length_expr`, maximum length of the new array (minimum is fixed at zero
///   for now)
/// `element_type`, actual element type of the array (the array for all
///   reference types will have void* type, but this will be annotated as the
///   true member type)
/// \return Appends instructions to `assignments`
void java_object_factoryt::allocate_nondet_length_array(
  code_blockt &assignments,
  const exprt &lhs,
  const exprt &max_length_expr,
  const typet &element_type)
{
  symbolt &length_sym=new_tmp_symbol(
    symbol_table,
    loc,
    java_int_type(),
    "nondet_array_length");
  symbols_created.push_back(&length_sym);
  const auto &length_sym_expr=length_sym.symbol_expr();

  // Initialize array with some undetermined length:
  gen_nondet_init(
    assignments,
    length_sym_expr,
    false,
    irep_idt(),
    false,
    false,
    false,
    typet(),
    NO_UPDATE_IN_PLACE);

  // Insert assumptions to bound its length:
  binary_relation_exprt
    assume1(length_sym_expr, ID_ge, from_integer(0, java_int_type()));
  binary_relation_exprt
    assume2(length_sym_expr, ID_le, max_length_expr);
  code_assumet assume_inst1(assume1);
  code_assumet assume_inst2(assume2);
  assignments.move_to_operands(assume_inst1);
  assignments.move_to_operands(assume_inst2);

  side_effect_exprt java_new_array(ID_java_new_array, lhs.type());
  java_new_array.copy_to_operands(length_sym_expr);
  java_new_array.set(ID_length_upper_bound, max_length_expr);
  java_new_array.type().subtype().set(ID_C_element_type, element_type);
  codet assign=code_assignt(lhs, java_new_array);
  assign.add_source_location()=loc;
  assignments.copy_to_operands(assign);
}

/// create code to initialize a Java array with size `max_nondet_array_length`,
/// loop over elements and initialize them
void java_object_factoryt::gen_nondet_array_init(
  code_blockt &assignments,
  const exprt &expr,
  update_in_placet update_in_place)
{
  assert(expr.type().id()==ID_pointer);
  assert(update_in_place!=MAY_UPDATE_IN_PLACE);
  const typet &type=ns.follow(expr.type().subtype());
  const struct_typet &struct_type=to_struct_type(type);
  assert(expr.type().subtype().id()==ID_symbol);
  const typet &element_type=
    static_cast<const typet &>(expr.type().subtype().find(ID_C_element_type));

  auto max_length_expr=from_integer(max_nondet_array_length, java_int_type());

  if(update_in_place==NO_UPDATE_IN_PLACE)
  {
    allocate_nondet_length_array(
      assignments,
      expr,
      max_length_expr,
      element_type);
  }

  // Otherwise we're updating the array in place, and use the
  // existing array allocation and length.

  dereference_exprt deref_expr(expr, expr.type().subtype());
  const auto &comps=struct_type.components();
  exprt length_expr=member_exprt(deref_expr, "length", comps[1].type());
  exprt init_array_expr=member_exprt(deref_expr, "data", comps[2].type());

  if(init_array_expr.type()!=pointer_type(element_type))
    init_array_expr=
      typecast_exprt(init_array_expr, pointer_type(element_type));

  // Interpose a new symbol, as the goto-symex stage can't handle array indexing
  // via a cast.
  symbolt &array_init_symbol=new_tmp_symbol(
    symbol_table,
    loc,
    init_array_expr.type(),
    "array_data_init");
  symbols_created.push_back(&array_init_symbol);
  const auto &array_init_symexpr=array_init_symbol.symbol_expr();
  codet data_assign=code_assignt(array_init_symexpr, init_array_expr);
  data_assign.add_source_location()=loc;
  assignments.copy_to_operands(data_assign);

  // Emit init loop for(array_init_iter=0; array_init_iter!=array.length;
  //                  ++array_init_iter) init(array[array_init_iter]);
  symbolt &counter=new_tmp_symbol(
    symbol_table,
    loc,
    length_expr.type(),
    "array_init_iter");
  symbols_created.push_back(&counter);
  exprt counter_expr=counter.symbol_expr();

  exprt java_zero=from_integer(0, java_int_type());
  assignments.copy_to_operands(code_assignt(counter_expr, java_zero));

  std::string head_name=as_string(counter.base_name)+"_header";
  code_labelt init_head_label(head_name, code_skipt());
  code_gotot goto_head(head_name);

  assignments.move_to_operands(init_head_label);

  std::string done_name=as_string(counter.base_name)+"_done";
  code_labelt init_done_label(done_name, code_skipt());
  code_gotot goto_done(done_name);

  code_ifthenelset done_test;
  done_test.cond()=equal_exprt(counter_expr, length_expr);
  done_test.then_case()=goto_done;

  assignments.move_to_operands(done_test);

  if(update_in_place!=MUST_UPDATE_IN_PLACE)
  {
    // Add a redundant if(counter == max_length) break
    // that is easier for the unwinder to understand.
    code_ifthenelset max_test;
    max_test.cond()=equal_exprt(counter_expr, max_length_expr);
    max_test.then_case()=goto_done;

    assignments.move_to_operands(max_test);
  }

  exprt arraycellref=dereference_exprt(
    plus_exprt(array_init_symexpr, counter_expr, array_init_symexpr.type()),
    array_init_symexpr.type().subtype());

  // MUST_UPDATE_IN_PLACE only applies to this object.
  // If this is a pointer to another object, offer the chance
  // to leave it alone by setting MAY_UPDATE_IN_PLACE instead.
  update_in_placet child_update_in_place=
    update_in_place==MUST_UPDATE_IN_PLACE ?
    MAY_UPDATE_IN_PLACE :
    update_in_place;
  gen_nondet_init(
    assignments,
    arraycellref,
    false,
    irep_idt(),
    false,
    true,
    true,
    element_type,
    child_update_in_place);

  exprt java_one=from_integer(1, java_int_type());
  code_assignt incr(counter_expr, plus_exprt(counter_expr, java_one));

  assignments.move_to_operands(incr);
  assignments.move_to_operands(goto_head);
  assignments.move_to_operands(init_done_label);
}

/// Similar to `gen_nondet_init` above, but always creates a fresh static global
/// object or primitive nondet expression.
/// \par parameters: `type`: type of new object to create
/// `allow_null`: if true, may return null; otherwise always allocates an object
/// `max_nondet_array_length`: upper bound on size of initialised arrays.
/// `loc`: source location for all generated code
/// `message_handler`: logging
/// \return `symbol_table` gains any new symbols created, as per gen_nondet_init
///   above. `init_code` gains any instructions requried to initialise either
///   the returned value or its child objects
exprt object_factory(
  const typet &type,
  const irep_idt base_name,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table,
  size_t max_nondet_array_length,
  const source_locationt &loc)
{
  irep_idt identifier=id2string(goto_functionst::entry_point())+
    "::"+id2string(base_name);

  auxiliary_symbolt main_symbol;
  main_symbol.mode=ID_java;
  main_symbol.is_static_lifetime=false;
  main_symbol.name=identifier;
  main_symbol.base_name=base_name;
  main_symbol.type=type;
  main_symbol.location=loc;

  exprt object=main_symbol.symbol_expr();

  symbolt *main_symbol_ptr;
  bool moving_symbol_failed=symbol_table.move(main_symbol, main_symbol_ptr);
  assert(!moving_symbol_failed);

  std::vector<const symbolt *> symbols_created;
  symbols_created.push_back(main_symbol_ptr);
  java_object_factoryt state(
    symbols_created,
    loc,
    !allow_null,
    max_nondet_array_length,
    symbol_table);
  code_blockt assignments;
  state.gen_nondet_init(
    assignments,
    object,
    false,
    "",
    false,
    false,
    false,
    typet(),
    NO_UPDATE_IN_PLACE);

  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt * const symbol_ptr : symbols_created)
  {
    code_declt decl(symbol_ptr->symbol_expr());
    decl.add_source_location()=loc;
    init_code.add(decl);
  }

  init_code.append(assignments);
  return object;
}

/// Initialises a primitive or object tree rooted at `expr`, allocating child
/// objects as necessary and nondet-initialising their members, or if MAY_ or
/// MUST_UPDATE_IN_PLACE is set, re-initialising already-allocated objects.
/// \par parameters: `expr`: lvalue expression to initialise
/// `loc`: source location for all generated code
/// `skip_classid`: if true, skip initialising @class_identifier
/// `create_dyn_objs`: if true, use malloc to allocate objects; otherwise
///   generate fresh static symbols.
/// `assume_non_null`: never initialise pointer members with null, unless forced
///   to by recursive datatypes
/// `message_handler`: logging
/// `max_nondet_array_length`: upper bound on size of initialised arrays.
/// `update_in_place`: NO_UPDATE_IN_PLACE: initialise `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialise an existing object MAY_UPDATE_IN_PLACE:
///   generate a runtime nondet branch between the NO_ and MUST_ cases.
/// \return `init_code` gets an instruction sequence to initialise or
///   reinitialise `expr` and child objects it refers to. `symbol_table` is
///   modified with any new symbols created. This includes any necessary
///   temporaries, and if `create_dyn_objs` is false, any allocated objects.
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  bool skip_classid,
  bool create_dyn_objs,
  bool assume_non_null,
  size_t max_nondet_array_length,
  update_in_placet update_in_place)
{
  std::vector<const symbolt *> symbols_created;

  java_object_factory_with_randomt state(
    symbols_created,
    loc,
    assume_non_null,
    max_nondet_array_length,
    symbol_table);
  code_blockt assignments;
  state.gen_nondet_init(
    assignments,
    expr,
    false,
    "",
    skip_classid,
    create_dyn_objs,
    false,
    typet(),
    update_in_place);

  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt * const symbol_ptr : symbols_created)
  {
    code_declt decl(symbol_ptr->symbol_expr());
    decl.add_source_location()=loc;
    init_code.add(decl);
  }

  init_code.append(assignments);
}


void java_object_factory_with_randomt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  bool create_dynamic_objects,
  bool override,
  const typet &override_type,
  update_in_placet update_in_place)
{
  const typet &type=
    override ? ns.follow(override_type) : ns.follow(expr.type());
  typet real_type=type;

  if(type.id()==ID_pointer && type.subtype().id()==ID_symbol)
  {
    const pointer_typet &pointer_type=to_pointer_type(type);
    const namespacet ns(symbol_table);

    select_pointer_typet pointer_type_selector(ns);
    const pointer_typet &replacement_pointer=
      pointer_type_selector(pointer_type);

    if(replacement_pointer!=real_type)
    {
      // Generate GOTO code to initalize the selected concrete type
      // A { ... } tmp_object;
      // A.x = NONDET ...
      // // non-det init of all the fields of A
      // A * p = &tmp_object
      // expr = (I *)p

      symbolt new_symbol=new_tmp_symbol(symbol_table, loc, replacement_pointer);

      // Generate a new object into this new symbol
      gen_nondet_init(
        assignments,
        new_symbol.symbol_expr(),
        is_sub,
        class_identifier,
        skip_classid,
        create_dynamic_objects,
        override,
        override_type,
        update_in_placet::NO_UPDATE_IN_PLACE);

      assignments.add(
        code_assignt(expr, typecast_exprt(new_symbol.symbol_expr(), type)));

      return;
    }
  }
  java_object_factoryt::gen_nondet_init(
    assignments,
    expr,
    is_sub,
    class_identifier,
    skip_classid,
    create_dynamic_objects,
    override,
    override_type,
    update_in_place);
}
