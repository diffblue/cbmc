/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_object_factory.h"

#include <util/expr_initializer.h>
#include <util/fresh_symbol.h>
#include <util/nondet_bool.h>
#include <util/nondet.h>
#include <util/pointer_offset_size.h>

#include <goto-programs/class_identifier.h>
#include <goto-programs/goto_functions.h>

#include "generic_parameter_specialization_map_keys.h"
#include "java_root_class.h"
#include "java_string_literals.h"

class java_object_factoryt
{
  /// The source location for new statements emitted during the operation of the
  /// methods in this class.
  const source_locationt &loc;

  const java_object_factory_parameterst object_factory_parameters;

  /// This is employed in conjunction with the depth above. Every time the
  /// non-det generator visits a type, the type is added to this set. We forbid
  /// the non-det initialization when we see the type for the second time in
  /// this set AND the tree depth becomes >= than the maximum value above.
  std::unordered_set<irep_idt> recursion_set;

  /// Every time the non-det generator visits a type and the type is generic
  /// (either a struct or a pointer), the following map is used to store and
  /// look up the concrete types of the generic parameters in the current
  /// scope. Note that not all generic parameters need to have a concrete
  /// type, e.g., the method under test is generic. The types are removed
  /// from the map when the scope changes. Note that in different depths
  /// of the scope the parameters can be specialized with different types
  /// so we keep a stack of types for each parameter.
  generic_parameter_specialization_mapt generic_parameter_specialization_map;

  /// The symbol table.
  symbol_table_baset &symbol_table;

  /// A namespace built from exclusively one symbol table - the one above.
  namespacet ns;

  /// Resolves pointer types potentially using some heuristics, for example
  /// to replace pointers to interface types with pointers to concrete
  /// implementations.
  const select_pointer_typet &pointer_type_selector;

  allocate_objectst allocate_objects;

  code_assignt get_null_assignment(
    const exprt &expr,
    const pointer_typet &ptr_type);

  void gen_pointer_target_init(
    code_blockt &assignments,
    const exprt &expr,
    const typet &target_type,
    lifetimet lifetime,
    size_t depth,
    update_in_placet update_in_place,
    const source_locationt &location);

  void allocate_nondet_length_array(
    code_blockt &assignments,
    const exprt &lhs,
    const exprt &max_length_expr,
    const typet &element_type,
    const source_locationt &location);

public:
  java_object_factoryt(
    const source_locationt &loc,
    const java_object_factory_parameterst _object_factory_parameters,
    symbol_table_baset &_symbol_table,
    const select_pointer_typet &pointer_type_selector)
    : loc(loc),
      object_factory_parameters(_object_factory_parameters),
      symbol_table(_symbol_table),
      ns(_symbol_table),
      pointer_type_selector(pointer_type_selector),
      allocate_objects(
        ID_java,
        loc,
        object_factory_parameters.function_id,
        symbol_table)
  {}

  void gen_nondet_array_init(
    code_blockt &assignments,
    const exprt &expr,
    size_t depth,
    update_in_placet,
    const source_locationt &location);

  void gen_nondet_enum_init(
    code_blockt &assignments,
    const exprt &expr,
    const java_class_typet &java_class_type,
    const source_locationt &location);

  void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    bool is_sub,
    irep_idt class_identifier,
    bool skip_classid,
    lifetimet lifetime,
    const optionalt<typet> &override_type,
    size_t depth,
    update_in_placet,
    const source_locationt &location);

  void add_created_symbol(const symbolt *symbol);

  void declare_created_symbols(code_blockt &init_code);

private:
  void gen_nondet_pointer_init(
    code_blockt &assignments,
    const exprt &expr,
    lifetimet lifetime,
    const pointer_typet &pointer_type,
    size_t depth,
    const update_in_placet &update_in_place,
    const source_locationt &location);

  void gen_nondet_struct_init(
    code_blockt &assignments,
    const exprt &expr,
    bool is_sub,
    irep_idt class_identifier,
    bool skip_classid,
    lifetimet lifetime,
    const struct_typet &struct_type,
    size_t depth,
    const update_in_placet &update_in_place,
    const source_locationt &location);

  symbol_exprt gen_nondet_subtype_pointer_init(
    code_blockt &assignments,
    lifetimet lifetime,
    const pointer_typet &substitute_pointer_type,
    size_t depth,
    const source_locationt &location);

  const symbol_exprt gen_nondet_int_init(
    code_blockt &assignments,
    const std::string &basename_prefix,
    const exprt &min_length_expr,
    const exprt &max_length_expr,
    const source_locationt &location);

  void gen_method_call_if_present(
    code_blockt &assignments,
    const exprt &instance_expr,
    const irep_idt &method_name);

  void array_primitive_init_code(
    code_blockt &assignments,
    const exprt &init_array_expr,
    const typet &element_type,
    const exprt &max_length_expr,
    const source_locationt &location);

  void array_loop_init_code(
    code_blockt &assignments,
    const exprt &init_array_expr,
    const exprt &length_expr,
    const typet &element_type,
    const exprt &max_length_expr,
    size_t depth,
    update_in_placet update_in_place,
    const source_locationt &location);
};

/// Returns a codet that assigns \p expr, of type \p ptr_type, a NULL value.
code_assignt java_object_factoryt::get_null_assignment(
  const exprt &expr,
  const pointer_typet &ptr_type)
{
  null_pointer_exprt null_pointer_expr(ptr_type);
  code_assignt code(expr, null_pointer_expr);
  code.add_source_location()=loc;
  return code;
}

/// Initializes the pointer-typed lvalue expression `expr` to point to an object
/// of type `target_type`, recursively nondet-initializing the members of that
/// object. Code emitted mainly depends on \p update_in_place:
///
/// When in NO_UPDATE_IN_PLACE mode, the code emitted looks like:
///
/// \code
///   struct new_object obj; // depends on lifetime
///   <expr> := &obj
///   // recursive initialization of obj in NO_UPDATE_IN_PLACE mode
/// \endcode
///
/// When in MUST_UPDATE_IN_PLACE mode, all code is emitted by a recursive call
/// to gen_nondet_init in MUST_UPDATE_IN_PLACE mode, and looks like:
///
/// \code
///   (*<expr>).some_int := NONDET(int)
///   (*<expr>).some_char := NONDET(char)
/// \endcode
/// It is illegal to call the function with MAY_UPDATE_IN_PLACE.
///
/// \param [out] assignments:
///   A code_blockt where the initialization code will be emitted to.
/// \param expr:
///   Pointer-typed lvalue expression to initialize.
///   The pointed type equals \p target_type.
/// \param target_type:
///   Structure type to initialize, which may not match `*expr` (for example,
///   `expr` might be have type void*). It cannot be a pointer to a primitive
///   type because Java does not allow so.
/// \param lifetime:
///   Lifetime of the allocated objects (AUTOMATIC_LOCAL, STATIC_GLOBAL, or
///   DYNAMIC)
/// \param depth:
///   Number of times that a pointer has been dereferenced from the root of the
///   object tree that we are initializing.
/// \param update_in_place:
///   NO_UPDATE_IN_PLACE: initialize `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialize an existing object
///   MAY_UPDATE_IN_PLACE: invalid input
/// \param location:
///   Source location associated with nondet-initialization.
void java_object_factoryt::gen_pointer_target_init(
  code_blockt &assignments,
  const exprt &expr,
  const typet &target_type,
  lifetimet lifetime,
  size_t depth,
  update_in_placet update_in_place,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(update_in_place != update_in_placet::MAY_UPDATE_IN_PLACE);

  if(target_type.id() == ID_struct)
  {
    const auto &target_class_type = to_java_class_type(target_type);
    if(has_prefix(id2string(target_class_type.get_tag()), "java::array["))
    {
      gen_nondet_array_init(
        assignments, expr, depth + 1, update_in_place, location);
      return;
    }
    if(target_class_type.get_base("java::java.lang.Enum"))
    {
      gen_nondet_enum_init(assignments, expr, target_class_type, location);
      return;
    }
  }

  // obtain a target pointer to initialize; if in MUST_UPDATE_IN_PLACE mode we
  // initialize the fields of the object pointed by `expr`; if in
  // NO_UPDATE_IN_PLACE then we allocate a new object, get a pointer to it
  // (return value of `allocate_object`), emit a statement of the form
  // `<expr> := address-of(<new-object>)` and recursively initialize such new
  // object.
  exprt init_expr;
  if(update_in_place == update_in_placet::NO_UPDATE_IN_PLACE)
  {
    init_expr = allocate_objects.allocate_object(
      assignments, expr, target_type, lifetime, "tmp_object_factory");
  }
  else
  {
    if(expr.id() == ID_address_of)
      init_expr = expr.op0();
    else
    {
      init_expr = dereference_exprt(expr);
    }
  }

  gen_nondet_init(
    assignments,
    init_expr,
    false, // is_sub
    "",    // class_identifier
    false, // skip_classid
    lifetime,
    {}, // no override type
    depth + 1,
    update_in_place,
    location);
}

/// Recursion-set entry owner class. If a recursion-set entry is added
/// in a particular scope, ensures that it is erased on leaving
/// that scope.
class recursion_set_entryt
{
  /// Recursion set to modify
  std::unordered_set<irep_idt> &recursion_set;
  /// Entry to erase on destruction, if non-empty
  irep_idt erase_entry;

public:
  /// Initialize a recursion-set entry owner operating on a given set.
  /// Initially it does not own any set entry.
  /// \param _recursion_set: set to operate on.
  explicit recursion_set_entryt(std::unordered_set<irep_idt> &_recursion_set)
    : recursion_set(_recursion_set)
  { }

  /// Removes erase_entry (if set) from the controlled set.
  ~recursion_set_entryt()
  {
    if(erase_entry!=irep_idt())
      recursion_set.erase(erase_entry);
  }

  recursion_set_entryt(const recursion_set_entryt &)=delete;
  recursion_set_entryt &operator=(const recursion_set_entryt &)=delete;

  /// Try to add an entry to the controlled set. If it is added, own that
  /// entry and erase it on destruction; otherwise do nothing.
  /// \param entry: entry to add
  /// \return true if added to the set (and therefore owned by this object)
  bool insert_entry(const irep_idt &entry)
  {
    INVARIANT(
      erase_entry==irep_idt(),
      "insert_entry should only be called once");
    INVARIANT(entry!=irep_idt(), "entry should be a struct tag");
    bool ret=recursion_set.insert(entry).second;
    if(ret)
    {
      // We added something, so erase it when this is destroyed:
      erase_entry=entry;
    }
    return ret;
  }
};

/// Get max value for an integer type
/// \param type:
///   Type to find maximum value for
/// \return Maximum integer value
static mp_integer max_value(const typet &type)
{
  if(type.id() == ID_signedbv)
    return to_signedbv_type(type).largest();
  else if(type.id() == ID_unsignedbv)
    return to_unsignedbv_type(type).largest();
  UNREACHABLE;
}

/// Initialise length and data fields for a nondeterministic String structure.
///
/// If the structure is not a nondeterministic structure, the call results in
/// a precondition violation.
/// \param [out] struct_expr: struct that we initialize
/// \param code: block to add pre-requisite declarations (e.g. to allocate a
///   data array)
/// \param min_nondet_string_length: minimum length of strings to initialize
/// \param max_nondet_string_length: maximum length of strings to initialize
/// \param loc: location in the source
/// \param function_id: function ID to associate with auxiliary variables
/// \param symbol_table: the symbol table
/// \param printable: if true, the nondet string must consist of printable
///   characters only
///
/// The code produced is of the form:
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// int tmp_object_factory$1;
/// tmp_object_factory$1 = NONDET(int);
/// __CPROVER_assume(tmp_object_factory$1 >= 0);
/// __CPROVER_assume(tmp_object_factory$1 <= max_nondet_string_length);
/// char (*string_data_pointer)[INFINITY()];
/// string_data_pointer = ALLOCATE(char [INFINITY()], INFINITY(), false);
/// char nondet_infinite_array$2[INFINITY()];
/// nondet_infinite_array$2 = NONDET(char [INFINITY()]);
/// *string_data_pointer = nondet_infinite_array$2;
/// cprover_associate_array_to_pointer_func(
///   *string_data_pointer, *string_data_pointer);
/// cprover_associate_length_to_array_func(
///   *string_data_pointer, tmp_object_factory);
///
/// struct_expr is then adjusted to set
///   .length=tmp_object_factory,
///   .data=*string_data_pointer
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// Unit tests in `unit/java_bytecode/java_object_factory/` ensure
/// it is the case.
void initialize_nondet_string_fields(
  struct_exprt &struct_expr,
  code_blockt &code,
  const std::size_t &min_nondet_string_length,
  const std::size_t &max_nondet_string_length,
  const source_locationt &loc,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  bool printable)
{
  PRECONDITION(
    java_string_library_preprocesst
      ::implements_java_char_sequence(struct_expr.type()));

  namespacet ns(symbol_table);

  const struct_typet &struct_type =
    to_struct_type(ns.follow(struct_expr.type()));

  // In case the type for String was not added to the symbol table,
  // (typically when string refinement is not activated), `struct_type`
  // just contains the standard Object fields (or may have some other model
  // entirely), and in particular has no length and data fields.
  PRECONDITION(
    struct_type.has_component("length") && struct_type.has_component("data"));

  // We allow type StringBuffer and StringBuilder to be initialized
  // in the same way has String, because they have the same structure and
  // are treated in the same way by CBMC.

  // Note that CharSequence cannot be used as classid because it's abstract,
  // so it is replaced by String.
  // \todo allow StringBuffer and StringBuilder as classid for Charsequence
  if(struct_type.get_tag() == "java.lang.CharSequence")
  {
    set_class_identifier(
      struct_expr, ns, struct_tag_typet("java::java.lang.String"));
  }

  // OK, this is a String type with the expected fields -- add code to `code`
  // to set up pre-requisite variables and assign them in `struct_expr`.

  /// \todo Refactor with make_nondet_string_expr
  // length_expr = nondet(int);
  const symbolt length_sym = get_fresh_aux_symbol(
    java_int_type(),
    id2string(function_id),
    "tmp_object_factory",
    loc,
    ID_java,
    symbol_table);
  const symbol_exprt length_expr = length_sym.symbol_expr();
  const side_effect_expr_nondett nondet_length(length_expr.type(), loc);
  code.add(code_declt(length_expr));
  code.add(code_assignt(length_expr, nondet_length));

  // assume (length_expr >= min_nondet_string_length);
  const exprt min_length =
    from_integer(min_nondet_string_length, java_int_type());
  code.add(code_assumet(binary_relation_exprt(length_expr, ID_ge, min_length)));

  // assume (length_expr <= max_input_length)
  if(max_nondet_string_length <= max_value(length_expr.type()))
  {
    exprt max_length =
      from_integer(max_nondet_string_length, length_expr.type());
    code.add(
      code_assumet(binary_relation_exprt(length_expr, ID_le, max_length)));
  }

  const exprt data_expr =
    make_nondet_infinite_char_array(symbol_table, loc, function_id, code);
  struct_expr.operands()[struct_type.component_number("length")] = length_expr;

  const address_of_exprt array_pointer(
    index_exprt(data_expr, from_integer(0, java_int_type())));

  add_pointer_to_array_association(
    array_pointer, data_expr, symbol_table, loc, code);

  add_array_to_length_association(
    data_expr, length_expr, symbol_table, loc, code);

  struct_expr.operands()[struct_type.component_number("data")] = array_pointer;

  // Printable ASCII characters are between ' ' and '~'.
  if(printable)
  {
    add_character_set_constraint(
      array_pointer, length_expr, " -~", symbol_table, loc, code);
  }
}

/// Initializes a pointer \p expr of type \p pointer_type to a primitive-typed
/// value or an object tree.  It allocates child objects as necessary and
/// nondet-initializes their members, or if MUST_UPDATE_IN_PLACE is set,
/// re-initializes already-allocated objects.
///
/// \param assignments:
///   The code block we are building with initialization code.
/// \param expr:
///   Pointer-typed lvalue expression to initialize.
/// \param lifetime:
///   Lifetime of the allocated objects (AUTOMATIC_LOCAL, STATIC_GLOBAL, or
///   DYNAMIC)
/// \param depth:
///   Number of times that a pointer has been dereferenced from the root of the
///   object tree that we are initializing.
/// \param pointer_type:
///   The type of the pointer we are initalizing
/// \param update_in_place:
///   * NO_UPDATE_IN_PLACE: initialize `expr` from scratch
///   * MAY_UPDATE_IN_PLACE: generate a runtime nondet branch between the NO_
///     and MUST_ cases.
///   * MUST_UPDATE_IN_PLACE: reinitialize an existing object
/// \param location:
///   Source location associated with nondet-initialization.
void java_object_factoryt::gen_nondet_pointer_init(
  code_blockt &assignments,
  const exprt &expr,
  lifetimet lifetime,
  const pointer_typet &pointer_type,
  size_t depth,
  const update_in_placet &update_in_place,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id()==ID_pointer);
  const pointer_typet &replacement_pointer_type =
    pointer_type_selector.convert_pointer_type(
      pointer_type, generic_parameter_specialization_map, ns);

  // If we are changing the pointer, we generate code for creating a pointer
  // to the substituted type instead
  // TODO if we are comparing array types we need to compare their element
  // types. this is for now done by implementing equality function especially
  // for java types, technical debt TG-2707
  if(!equal_java_types(replacement_pointer_type, pointer_type))
  {
    // update generic_parameter_specialization_map for the new pointer
    generic_parameter_specialization_map_keyst
      generic_parameter_specialization_map_keys(
        generic_parameter_specialization_map);
    generic_parameter_specialization_map_keys.insert_pairs_for_pointer(
      replacement_pointer_type, ns.follow(replacement_pointer_type.subtype()));

    const symbol_exprt real_pointer_symbol = gen_nondet_subtype_pointer_init(
      assignments, lifetime, replacement_pointer_type, depth, location);

    // Having created a pointer to object of type replacement_pointer_type
    // we now assign it back to the original pointer with a cast
    // from pointer_type to replacement_pointer_type
    assignments.add(
      code_assignt(expr, typecast_exprt(real_pointer_symbol, pointer_type)));
    return;
  }

  // This deletes the recursion set entry on leaving this function scope,
  // if one is set below.
  recursion_set_entryt recursion_set_entry(recursion_set);

  // If the pointed value is struct-typed, then we need to prevent the
  // possibility of this code to loop infinitely when initializing a data
  // structure with recursive types or unbounded depth.  We implement two
  // mechanisms here. We keep a set of 'types seen', and detect when we perform
  // a 2nd visit to the same type.  We also detect the depth in the chain of
  // (recursive) calls to the methods of this class. The depth counter is
  // incremented only when a pointer is deferenced, including pointers to
  // arrays.
  //
  // When we visit for 2nd time a type AND the maximum depth is exceeded, we set
  // the pointer to NULL instead of recursively initializing the struct to which
  // it points.
  const typet &subtype=ns.follow(pointer_type.subtype());
  if(subtype.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(subtype);
    const irep_idt &struct_tag=struct_type.get_tag();

    // If this is a recursive type of some kind AND the depth is exceeded, set
    // the pointer to null.
    if(!recursion_set_entry.insert_entry(struct_tag) &&
      depth>=object_factory_parameters.max_nondet_tree_depth)
    {
      if(update_in_place==update_in_placet::NO_UPDATE_IN_PLACE)
      {
        assignments.add(get_null_assignment(expr, pointer_type));
      }
      // Otherwise leave it as it is.
      return;
    }
  }

  // If this is a void* we *must* initialise with null:
  // (This can currently happen for some cases of #exception_value)
  bool must_be_null = subtype == empty_typet();

  // If we may be about to initialize a non-null enum type, always run the
  // clinit_wrapper of its class first.
  // TODO: TG-4689 we may want to do this for all types, not just enums, as
  // described in the Java language specification:
  // https://docs.oracle.com/javase/specs/jls/se8/html/jls-8.html#jls-8.7
  // https://docs.oracle.com/javase/specs/jls/se8/html/jls-12.html#jls-12.4.1
  // But we would have to put this behavior behind an option as it would have an
  // impact on running times.
  // Note that it would be more consistent with the behaviour of the JVM to only
  // run clinit_wrapper if we are about to initialize an object of which we know
  // for sure that it is not null on any following branch. However, adding this
  // case in gen_nondet_struct_init would slow symex down too much, so if we
  // decide to do this for all types, we should do it here.
  // Note also that this logic is mirrored in
  // ci_lazy_methodst::initialize_instantiated_classes.
  if(const auto class_type = type_try_dynamic_cast<java_class_typet>(subtype))
  {
    if(class_type->get_base("java::java.lang.Enum") && !must_be_null)
    {
      const irep_idt &class_name = class_type->get_name();
      const irep_idt class_clinit = clinit_wrapper_name(class_name);
      gen_method_call_if_present(assignments, expr, class_clinit);
    }
  }

  code_blockt new_object_assignments;
  code_blockt update_in_place_assignments;

  // if the initialization mode is MAY_UPDATE or MUST_UPDATE in place, then we
  // emit to `update_in_place_assignments` code for in-place initialization of
  // the object pointed by `expr`, assuming that such object is of type
  // `subtype`
  if(update_in_place!=update_in_placet::NO_UPDATE_IN_PLACE)
  {
    gen_pointer_target_init(
      update_in_place_assignments,
      expr,
      subtype,
      lifetime,
      depth,
      update_in_placet::MUST_UPDATE_IN_PLACE,
      location);
  }

  // if we MUST_UPDATE_IN_PLACE, then the job is done, we copy the code emitted
  // above to `assignments` and return
  if(update_in_place==update_in_placet::MUST_UPDATE_IN_PLACE)
  {
    assignments.append(update_in_place_assignments);
    return;
  }

  // if the mode is NO_UPDATE or MAY_UPDATE in place, then we need to emit a
  // vector of assignments that create a new object (recursively initializes it)
  // and asign to `expr` the address of such object
  code_blockt non_null_inst;

  gen_pointer_target_init(
    non_null_inst,
    expr,
    subtype,
    lifetime,
    depth,
    update_in_placet::NO_UPDATE_IN_PLACE,
    location);

  auto set_null_inst=get_null_assignment(expr, pointer_type);

  const bool allow_null = depth > object_factory_parameters.min_null_tree_depth;

  if(must_be_null)
  {
    // Add the following code to assignments:
    // <expr> = nullptr;
    new_object_assignments.add(set_null_inst);
  }
  else if(!allow_null)
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
    code_ifthenelset null_check(
      side_effect_expr_nondett(bool_typet(), location),
      std::move(set_null_inst),
      std::move(non_null_inst));

    new_object_assignments.add(std::move(null_check));
  }

  // Similarly to above, maybe use a conditional if both the
  // allocate-fresh and update-in-place cases are allowed:
  if(update_in_place==update_in_placet::NO_UPDATE_IN_PLACE)
  {
    assignments.append(new_object_assignments);
  }
  else
  {
    INVARIANT(update_in_place==update_in_placet::MAY_UPDATE_IN_PLACE,
      "No-update and must-update should have already been resolved");

    code_ifthenelset update_check(
      side_effect_expr_nondett(bool_typet(), expr.source_location()),
      std::move(update_in_place_assignments),
      std::move(new_object_assignments));

    assignments.add(std::move(update_check));
  }
}

/// Generate codet assignments to initalize the selected concrete type.
/// Generated code looks as follows (here A = replacement_pointer.subtype()):
///
///   // allocate memory for a new object, depends on `lifetime`
///   A { ... } tmp_object;
///
///   // non-det init all the fields of A
///   A.x = NONDET(...)
///   A.y = NONDET(...)
///
///   // assign `expr` with a suitably casted pointer to new_object
///   A * p = &tmp_object
///
/// \param assignments: A block of code where we append the generated code
/// \param lifetime: Lifetime of the allocated objects (AUTOMATIC_LOCAL,
///   STATIC_GLOBAL, or DYNAMIC)
/// \param replacement_pointer: The type of the pointer we actually want to
///   create
/// \param depth: Number of times that a pointer has been dereferenced from the
///   root of the object tree that we are initializing
/// \param location: Source location associated with nondet-initialization
/// \return A symbol expression of type \p replacement_pointer corresponding to
///   a pointer to object `tmp_object` (see above)
symbol_exprt java_object_factoryt::gen_nondet_subtype_pointer_init(
  code_blockt &assignments,
  lifetimet lifetime,
  const pointer_typet &replacement_pointer,
  size_t depth,
  const source_locationt &location)
{
  symbolt new_symbol = get_fresh_aux_symbol(
    replacement_pointer,
    id2string(object_factory_parameters.function_id),
    "tmp_object_factory",
    loc,
    ID_java,
    symbol_table);

  // Generate a new object into this new symbol
  gen_nondet_init(
    assignments,
    new_symbol.symbol_expr(),
    false, // is_sub
    "",    // class_identifier
    false, // skip_classid
    lifetime,
    {}, // no override_type
    depth,
    update_in_placet::NO_UPDATE_IN_PLACE,
    location);

  return new_symbol.symbol_expr();
}

/// Creates an alternate_casest vector in which each item contains an
/// assignment of a string from \p string_input_values (or more precisely the
/// literal symbol corresponding to the string) to \p expr.
/// \param expr:
///   Struct-typed lvalue expression to which we want to assign the strings.
/// \param string_input_values:
///   Strings to assign.
/// \param symbol_table:
///   The symbol table in which we'll lool up literal symbol
/// \return A vector that can be passed to generate_nondet_switch
alternate_casest get_string_input_values_code(
  const exprt &expr,
  const std::list<std::string> &string_input_values,
  symbol_table_baset &symbol_table)
{
  alternate_casest cases;
  for(const auto &val : string_input_values)
  {
    exprt name_literal(ID_java_string_literal);
    name_literal.set(ID_value, val);
    const symbol_exprt s =
      get_or_create_string_literal_symbol(name_literal, symbol_table, true);
    cases.push_back(code_assignt(expr, s));
  }
  return cases;
}

/// Initializes an object tree rooted at `expr`, allocating child objects as
/// necessary and nondet-initializes their members, or if MUST_UPDATE_IN_PLACE
/// is set, re-initializes already-allocated objects.
/// After initialization calls validation method
/// `expr.cproverNondetInitialize()` if it was provided by the user.
///
/// \param assignments: The code block to append the new instructions to
/// \param expr: Struct-typed lvalue expression to initialize
/// \param is_sub: If true, `expr` is a substructure of a larger object, which
///   in Java necessarily means a base class
/// \param class_identifier: Name of the parent class. Used to initialize the
///   `@class_identifier` among others
/// \param skip_classid: If true, skip initializing `@class_identifier`
/// \param lifetime: Lifetime of the allocated objects (AUTOMATIC_LOCAL,
///   STATIC_GLOBAL, or DYNAMIC)
/// \param struct_type: The type of the struct we are initializing
/// \param depth: Number of times that a pointer has been dereferenced from the
///   root of the object tree that we are initializing
/// \param update_in_place: Enum instance with the following meaning.
///   NO_UPDATE_IN_PLACE: initialize `expr` from scratch
///   MUST_UPDATE_IN_PLACE: reinitialize an existing object
///   MAY_UPDATE_IN_PLACE: invalid input
/// \param location: Source location associated with nondet-initialization
void java_object_factoryt::gen_nondet_struct_init(
  code_blockt &assignments,
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  lifetimet lifetime,
  const struct_typet &struct_type,
  size_t depth,
  const update_in_placet &update_in_place,
  const source_locationt &location)
{
  PRECONDITION(ns.follow(expr.type()).id()==ID_struct);
  PRECONDITION(struct_type.id()==ID_struct);

  typedef struct_typet::componentst componentst;
  const irep_idt &struct_tag=struct_type.get_tag();

  const componentst &components=struct_type.components();

  // Should we write the whole object?
  // * Not if this is a sub-structure (a superclass object), as our caller will
  //   have done this already
  // * Not if the object has already been initialised by our caller, in which
  //   case they will set `skip_classid`
  // * Not if we're re-initializing an existing object (i.e. update_in_place)

  bool skip_special_string_fields = false;

  if(!is_sub &&
     !skip_classid &&
     update_in_place != update_in_placet::MUST_UPDATE_IN_PLACE)
  {
    class_identifier = struct_tag;

    const bool is_char_sequence =
      java_string_library_preprocesst
        ::implements_java_char_sequence(struct_type);
    const bool has_length_and_data =
      struct_type.has_component("length") && struct_type.has_component("data");
    const bool has_string_input_values =
      !object_factory_parameters.string_input_values.empty();

    if(is_char_sequence && has_length_and_data && has_string_input_values)
    { // We're dealing with a string and we should set fixed input values.
      skip_special_string_fields = true;

      // We create a switch statement where each case is an assignment
      // of one of the fixed input strings to the input variable in question

      const alternate_casest cases =
        get_string_input_values_code(
          expr,
          object_factory_parameters.string_input_values,
          symbol_table);
      assignments.add(generate_nondet_switch(
        id2string(object_factory_parameters.function_id),
        cases,
        java_int_type(),
        ID_java,
        loc,
        symbol_table));
    }
    else
    {
      // Add an initial all-zero write. Most of the fields of this will be
      // overwritten, but it helps to have a whole-structure write that analysis
      // passes can easily recognise leaves no uninitialised state behind.

      // This code mirrors the `remove_java_new` pass:
      auto initial_object =
        zero_initializer(struct_type, source_locationt(), ns);
      CHECK_RETURN(initial_object.has_value());
      const irep_idt qualified_clsid = "java::" + id2string(class_identifier);
      set_class_identifier(
        to_struct_expr(*initial_object), ns, struct_tag_typet(qualified_clsid));

      // If the initialised type is a special-cased String type (one with length
      // and data fields introduced by string-library preprocessing), initialise
      // those fields with nondet values
      if(is_char_sequence && has_length_and_data)
      { // We're dealing with a string
        skip_special_string_fields = true;
        initialize_nondet_string_fields(
          to_struct_expr(*initial_object),
          assignments,
          object_factory_parameters.min_nondet_string_length,
          object_factory_parameters.max_nondet_string_length,
          loc,
          object_factory_parameters.function_id,
          symbol_table,
          object_factory_parameters.string_printable);
      }

      assignments.add(code_assignt(expr, *initial_object));
    }
  }

  for(const auto &component : components)
  {
    const typet &component_type=component.type();
    irep_idt name=component.get_name();

    member_exprt me(expr, name, component_type);

    if(name=="@class_identifier")
    {
      continue;
    }
    else if(name == "cproverMonitorCount")
    {
      // Zero-initialize 'cproverMonitorCount' field as it is not meant to be
      // nondet. This field is only present when the java core models are
      // included in the class-path. It is used to implement a critical section,
      // which is necessary to support concurrency.
      if(update_in_place == update_in_placet::MUST_UPDATE_IN_PLACE)
        continue;
      code_assignt code(me, from_integer(0, me.type()));
      code.add_source_location() = loc;
      assignments.add(code);
    }
    else if(skip_special_string_fields && (name == "length" || name == "data"))
    {
      // In this case these were set up above.
      continue;
    }
    else
    {
      INVARIANT(!name.empty(), "Each component of a struct must have a name");

      bool _is_sub=name[0]=='@';

      // MUST_UPDATE_IN_PLACE only applies to this object.
      // If this is a pointer to another object, offer the chance
      // to leave it alone by setting MAY_UPDATE_IN_PLACE instead.
      update_in_placet substruct_in_place=
        update_in_place==update_in_placet::MUST_UPDATE_IN_PLACE && !_is_sub ?
        update_in_placet::MAY_UPDATE_IN_PLACE :
        update_in_place;
      gen_nondet_init(
        assignments,
        me,
        _is_sub,
        class_identifier,
        false, // skip_classid
        lifetime,
        {}, // no override_type
        depth,
        substruct_in_place,
        location);
    }
  }

  // If <class_identifier>.cproverNondetInitialize() can be found in the
  // symbol table, we add a call:
  // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // expr.cproverNondetInitialize();
  // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  const irep_idt init_method_name =
    "java::" + id2string(struct_tag) + ".cproverNondetInitialize:()V";
  gen_method_call_if_present(assignments, expr, init_method_name);
}

/// Initializes a primitive-typed or reference-typed object tree rooted at
/// `expr`, allocating child objects as necessary and nondet-initializing their
/// members, or if MUST_UPDATE_IN_PLACE is set, re-initializing
/// already-allocated objects.
///
/// \param assignments:
///   A code block where the initializing assignments will be appended to.
/// \param expr:
///   Lvalue expression to initialize.
/// \param is_sub:
///   If true, `expr` is a substructure of a larger object, which in Java
///   necessarily means a base class.
/// \param class_identifier:
///   Name of the parent class. Used to initialize the `@class_identifier` among
///   others.
/// \param skip_classid:
///   If true, skip initializing `@class_identifier`.
/// \param lifetime:
///   Lifetime of the allocated objects (AUTOMATIC_LOCAL, STATIC_GLOBAL, or
///   DYNAMIC)
/// \param depth:
///   Number of times that a pointer has been dereferenced from the root of the
///   object tree that we are initializing.
/// \param override_type:
///   If not empty, initialize with `override_type` instead of `expr.type()`.
///   Used at the moment for reference arrays, which are implemented as
///   void* arrays but should be init'd as their true type with appropriate
///   casts.
/// \param update_in_place:
///   NO_UPDATE_IN_PLACE: initialize `expr` from scratch
///   MAY_UPDATE_IN_PLACE: generate a runtime nondet branch between the NO_
///   and MUST_ cases.
///   MUST_UPDATE_IN_PLACE: reinitialize an existing object
/// \param location:
///   Source location associated with nondet-initialization.
void java_object_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  lifetimet lifetime,
  const optionalt<typet> &override_type,
  size_t depth,
  update_in_placet update_in_place,
  const source_locationt &location)
{
  const typet &type = override_type.has_value() ? ns.follow(*override_type)
                                                : ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);

    // If we are about to initialize a generic pointer type, add its concrete
    // types to the map and delete them on leaving this function scope.
    generic_parameter_specialization_map_keyst
      generic_parameter_specialization_map_keys(
        generic_parameter_specialization_map);
    generic_parameter_specialization_map_keys.insert_pairs_for_pointer(
      pointer_type, ns.follow(pointer_type.subtype()));

    gen_nondet_pointer_init(
      assignments,
      expr,
      lifetime,
      pointer_type,
      depth,
      update_in_place,
      location);
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet struct_type=to_struct_type(type);

    // If we are about to initialize a generic class (as a superclass object
    // for a different object), add its concrete types to the map and delete
    // them on leaving this function scope.
    generic_parameter_specialization_map_keyst
      generic_parameter_specialization_map_keys(
        generic_parameter_specialization_map);
    if(is_sub)
    {
      const typet &symbol =
        override_type.has_value() ? *override_type : expr.type();
      PRECONDITION(symbol.id() == ID_struct_tag);
      generic_parameter_specialization_map_keys.insert_pairs_for_symbol(
        to_struct_tag_type(symbol), struct_type);
    }

    gen_nondet_struct_init(
      assignments,
      expr,
      is_sub,
      class_identifier,
      skip_classid,
      lifetime,
      struct_type,
      depth,
      update_in_place,
      location);
  }
  else
  {
    // types different from pointer or structure:
    // bool, int, float, byte, char, ...
    exprt rhs = type.id() == ID_c_bool ? get_nondet_bool(type, loc)
                                       : side_effect_expr_nondett(type, loc);
    code_assignt assign(expr, rhs);
    assign.add_source_location()=loc;

    assignments.add(assign);
  }
}

void java_object_factoryt::add_created_symbol(const symbolt *symbol_ptr)
{
  allocate_objects.add_created_symbol(symbol_ptr);
}

void java_object_factoryt::declare_created_symbols(code_blockt &init_code)
{
  allocate_objects.declare_created_symbols(init_code);
}

/// Nondeterministically initializes an int i in the range min <= i <= max,
/// where min is the integer represented by `min_value_expr` and max is the
/// integer represented by `max_value_expr`.
/// \param [out] assignments: A code block that the initializing assignments
///   will be appended to.
/// \param basename_prefix: Used for naming the newly created symbol.
/// \param min_value_expr: Represents the minimum value for the integer.
/// \param max_value_expr: Represents the maximum value for the integer.
/// \param location: Source location associated with nondet-initialization.
/// \return A symbol expression for the resulting integer.
const symbol_exprt java_object_factoryt::gen_nondet_int_init(
  code_blockt &assignments,
  const std::string &basename_prefix,
  const exprt &min_value_expr,
  const exprt &max_value_expr,
  const source_locationt &location)
{
  PRECONDITION(min_value_expr.type() == max_value_expr.type());

  const symbol_exprt &int_symbol_expr =
    allocate_objects.allocate_automatic_local_object(
      min_value_expr.type(), basename_prefix);

  // Nondet-initialize it
  gen_nondet_init(
    assignments,
    int_symbol_expr,
    false, // is_sub
    irep_idt(),
    false,                      // skip_classid
    lifetimet::AUTOMATIC_LOCAL, // immaterial, type is primitive
    {},                         // no override type
    0,                          // depth is immaterial, always non-null
    update_in_placet::NO_UPDATE_IN_PLACE,
    location);

  // Insert assumptions to bound its value
  const auto min_assume_expr =
    binary_relation_exprt(int_symbol_expr, ID_ge, min_value_expr);
  const auto max_assume_expr =
    binary_relation_exprt(int_symbol_expr, ID_le, max_value_expr);
  assignments.add(code_assumet(min_assume_expr));
  assignments.add(code_assumet(max_assume_expr));

  return int_symbol_expr;
}

/// Allocates a fresh array and emits an assignment writing to \p lhs the
/// address of the new array.  Single-use at the moment, but useful to keep as a
/// separate function for downstream branches.
/// \param [out] assignments:
///   Code is emitted here.
/// \param lhs:
///   Symbol to assign the new array structure.
/// \param max_length_expr:
///   Maximum length of the new array (minimum is fixed at zero for now).
/// \param element_type:
///   Actual element type of the array (the array for all reference types will
///   have void* type, but this will be annotated as the true member type).
/// \param location:
///   Source location associated with nondet-initialization.
/// \return Appends instructions to `assignments`
void java_object_factoryt::allocate_nondet_length_array(
  code_blockt &assignments,
  const exprt &lhs,
  const exprt &max_length_expr,
  const typet &element_type,
  const source_locationt &location)
{
  const auto &length_sym_expr = gen_nondet_int_init(
    assignments,
    "nondet_array_length",
    from_integer(0, java_int_type()),
    max_length_expr,
    location);

  side_effect_exprt java_new_array(ID_java_new_array, lhs.type(), loc);
  java_new_array.copy_to_operands(length_sym_expr);
  java_new_array.set(ID_length_upper_bound, max_length_expr);
  java_new_array.type().subtype().set(ID_element_type, element_type);
  code_assignt assign(lhs, java_new_array);
  assign.add_source_location() = loc;
  assignments.add(assign);
}

/// Create code allocating object of size `size` and assigning it to `lhs`
/// \param lhs : pointer which will be allocated
/// \param size : size of the object
/// \return code allocation object and assigning `lhs`
codet make_allocate_code(const symbol_exprt &lhs, const exprt &size)
{
  side_effect_exprt alloc(ID_allocate, lhs.type(), lhs.source_location());
  alloc.add_to_operands(size);
  alloc.add_to_operands(false_exprt());
  return code_assignt(lhs, alloc);
}

/// Create code to nondeterministically initialize arrays of primitive type.
/// The code produced is of the form (for an array of type TYPE):
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///     TYPE (*array_data_init)[max_length_expr];
///     array_data_init =
///       ALLOCATE(TYPE [max_length_expr], max_length_expr, false);
///     *array_data_init = NONDET(TYPE [max_length_expr]);
///     init_array_expr = *array_data_init;
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// \param [out] assignments : Code block to which the initializing assignments
///   will be appended.
/// \param init_array_expr : array data
/// \param element_type: type of array elements
/// \param max_length_expr : the (constant) size to which initialise the array
/// \param location: Source location associated with nondet-initialization.
void java_object_factoryt::array_primitive_init_code(
  code_blockt &assignments,
  const exprt &init_array_expr,
  const typet &element_type,
  const exprt &max_length_expr,
  const source_locationt &location)
{
  const array_typet array_type(element_type, max_length_expr);

  // TYPE (*array_data_init)[max_length_expr];
  const symbol_exprt &tmp_finite_array_pointer =
    allocate_objects.allocate_automatic_local_object(
      pointer_type(array_type), "array_data_init");

  // array_data_init = ALLOCATE(TYPE [max_length_expr], max_length_expr, false);
  assignments.add(
    make_allocate_code(
      tmp_finite_array_pointer,
      max_length_expr));
  assignments.statements().back().add_source_location() = location;

  // *array_data_init = NONDET(TYPE [max_length_expr]);
  side_effect_expr_nondett nondet_data(array_type, loc);
  const dereference_exprt data_pointer_deref(
    tmp_finite_array_pointer, array_type);
  assignments.add(code_assignt(data_pointer_deref, std::move(nondet_data)));
  assignments.statements().back().add_source_location() = location;

  // init_array_expr = *array_data_init;
  address_of_exprt tmp_nondet_pointer(
    index_exprt(data_pointer_deref, from_integer(0, java_int_type())));
  assignments.add(code_assignt(init_array_expr, std::move(tmp_nondet_pointer)));
  assignments.statements().back().add_source_location() = location;
}

/// Create code to nondeterministically initialize each element of an array in a
/// loop.
/// The code produced is of the form (supposing an array of type OBJ):
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
///        struct OBJ **array_data_init;
///        int array_init_iter;
///        array_data_init = (struct OBJ **)init_array_expr;
///        array_init_iter = 0;
///     2: IF array_init_iter == length_expr THEN GOTO 5
///        IF array_init_iter == max_length_expr THEN GOTO 5
///        IF !NONDET(__CPROVER_bool) THEN GOTO 3
///        array_data_init[array_init_iter] = null;
///        GOTO 4
///     3: malloc_site = ALLOCATE(...);
///        array_data_init[array_init_iter] = (struct OBJ *)malloc_site;
///        *malloc_site = {...};
///        malloc_site->value = NONDET(int);
///     4: array_init_iter = array_init_iter + 1;
///        GOTO 2
///     5: ...
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/// \param [out] assignments : Code block to which the initializing assignments
///   will be appended.
/// \param init_array_expr : array data
/// \param length_expr : array length
/// \param element_type: type of array elements
/// \param max_length_expr : max length, as specified by max-nondet-array-length
/// \param depth: Number of times that a pointer has been dereferenced from the
///   root of the object tree that we are initializing.
/// \param update_in_place:
///   NO_UPDATE_IN_PLACE: initialize `expr` from scratch
///   MAY_UPDATE_IN_PLACE: generate a runtime nondet branch between the NO_
///   and MUST_ cases.
///   MUST_UPDATE_IN_PLACE: reinitialize an existing object
/// \param location: Source location associated with nondet-initialization.
void java_object_factoryt::array_loop_init_code(
  code_blockt &assignments,
  const exprt &init_array_expr,
  const exprt &length_expr,
  const typet &element_type,
  const exprt &max_length_expr,
  size_t depth,
  update_in_placet update_in_place,
  const source_locationt &location)
{
  const symbol_exprt &array_init_symexpr =
    allocate_objects.allocate_automatic_local_object(
      init_array_expr.type(), "array_data_init");

  code_assignt data_assign(array_init_symexpr, init_array_expr);
  data_assign.add_source_location()=loc;
  assignments.add(data_assign);

  const symbol_exprt &counter_expr =
    allocate_objects.allocate_automatic_local_object(
      length_expr.type(), "array_init_iter");

  const symbolt &counter =
    symbol_table.lookup_ref(counter_expr.get_identifier());

  exprt java_zero=from_integer(0, java_int_type());
  assignments.add(code_assignt(counter_expr, java_zero));

  std::string head_name = id2string(counter.base_name) + "_header";
  code_labelt init_head_label(head_name, code_skipt());
  code_gotot goto_head(head_name);

  assignments.add(std::move(init_head_label));

  std::string done_name = id2string(counter.base_name) + "_done";
  code_labelt init_done_label(done_name, code_skipt());
  code_gotot goto_done(done_name);

  code_ifthenelset done_test(equal_exprt(counter_expr, length_expr), goto_done);

  assignments.add(std::move(done_test));

  if(update_in_place!=update_in_placet::MUST_UPDATE_IN_PLACE)
  {
    // Add a redundant if(counter == max_length) break
    // that is easier for the unwinder to understand.
    code_ifthenelset max_test(
      equal_exprt(counter_expr, max_length_expr), std::move(goto_done));

    assignments.add(std::move(max_test));
  }

  const dereference_exprt arraycellref(
    plus_exprt(array_init_symexpr, counter_expr, array_init_symexpr.type()),
    array_init_symexpr.type().subtype());

  // MUST_UPDATE_IN_PLACE only applies to this object.
  // If this is a pointer to another object, offer the chance
  // to leave it alone by setting MAY_UPDATE_IN_PLACE instead.
  update_in_placet child_update_in_place=
    update_in_place==update_in_placet::MUST_UPDATE_IN_PLACE ?
    update_in_placet::MAY_UPDATE_IN_PLACE :
    update_in_place;
  gen_nondet_init(
    assignments,
    arraycellref,
    false,      // is_sub
    irep_idt(), // class_identifier
    false,      // skip_classid
    // These are variable in number, so use dynamic allocator:
    lifetimet::DYNAMIC,
    element_type, // override
    depth,
    child_update_in_place,
    location);

  exprt java_one=from_integer(1, java_int_type());
  code_assignt incr(counter_expr, plus_exprt(counter_expr, java_one));

  assignments.add(std::move(incr));
  assignments.add(std::move(goto_head));
  assignments.add(std::move(init_done_label));
}

/// Create code to initialize a Java array whose size will be at most
/// `max_nondet_array_length`. The code is emitted to \p assignments does as
/// follows:
/// 1. non-deterministically choose a length for the array
/// 2. assume that such length is >=0 and <= max_length
/// 3. loop through all elements of the array and initialize them
void java_object_factoryt::gen_nondet_array_init(
  code_blockt &assignments,
  const exprt &expr,
  size_t depth,
  update_in_placet update_in_place,
  const source_locationt &location)
{
  PRECONDITION(expr.type().id() == ID_pointer);
  PRECONDITION(expr.type().subtype().id() == ID_struct_tag);
  PRECONDITION(update_in_place != update_in_placet::MAY_UPDATE_IN_PLACE);

  const typet &type = ns.follow(expr.type().subtype());
  const struct_typet &struct_type = to_struct_type(type);
  const typet &element_type =
    static_cast<const typet &>(expr.type().subtype().find(ID_element_type));

  auto max_length_expr = from_integer(
    object_factory_parameters.max_nondet_array_length, java_int_type());

  // In NO_UPDATE_IN_PLACE mode we allocate a new array and recursively
  // initialize its elements
  if(update_in_place == update_in_placet::NO_UPDATE_IN_PLACE)
  {
    allocate_nondet_length_array(
      assignments, expr, max_length_expr, element_type, location);
  }

  // Otherwise we're updating the array in place, and use the
  // existing array allocation and length.

  INVARIANT(
    is_valid_java_array(struct_type),
    "Java struct array does not conform to expectations");

  dereference_exprt deref_expr(expr, expr.type().subtype());
  const auto &comps = struct_type.components();
  const member_exprt length_expr(deref_expr, "length", comps[1].type());
  exprt init_array_expr = member_exprt(deref_expr, "data", comps[2].type());

  if(init_array_expr.type() != pointer_type(element_type))
    init_array_expr =
      typecast_exprt(init_array_expr, pointer_type(element_type));

  array_loop_init_code(
    assignments,
    init_array_expr,
    length_expr,
    element_type,
    max_length_expr,
    depth,
    update_in_place,
    location);

  // TODO: Enable loop-less initialization of primitive arrays using
  // array_primitive_init_code
}

/// We nondet-initialize enums to be equal to one of the constants defined
/// for their type:
///     int i = nondet(int);
///     assume(0 < = i < $VALUES.length);
///     expr = $VALUES[i];
/// where $VALUES is a variable generated by the Java compiler that stores
/// the array that is returned by Enum.values().
void java_object_factoryt::gen_nondet_enum_init(
  code_blockt &assignments,
  const exprt &expr,
  const java_class_typet &java_class_type,
  const source_locationt &location)
{
  const irep_idt &class_name = java_class_type.get_name();
  const irep_idt values_name = id2string(class_name) + ".$VALUES";
  INVARIANT(
    ns.get_symbol_table().has_symbol(values_name),
    "The $VALUES array (populated by clinit_wrapper) should be in the "
    "symbol table");
  const symbolt &values = ns.lookup(values_name);

  // Access members (length and data) of $VALUES array
  dereference_exprt deref_expr(values.symbol_expr());
  const auto &deref_struct_type = to_struct_type(ns.follow(deref_expr.type()));
  PRECONDITION(is_valid_java_array(deref_struct_type));
  const auto &comps = deref_struct_type.components();
  const member_exprt length_expr(deref_expr, "length", comps[1].type());
  const member_exprt enum_array_expr =
    member_exprt(deref_expr, "data", comps[2].type());

  const symbol_exprt &index_expr = gen_nondet_int_init(
    assignments,
    "enum_index_init",
    from_integer(0, java_int_type()),
    minus_exprt(length_expr, from_integer(1, java_int_type())),
    location);

  // Generate statement using pointer arithmetic to access array element:
  // expr = (expr.type())*(enum_array_expr + index_expr);
  plus_exprt plus(enum_array_expr, index_expr);
  const dereference_exprt arraycellref(plus);
  code_assignt enum_assign(expr, typecast_exprt(arraycellref, expr.type()));
  assignments.add(enum_assign);
}

/// Similar to `gen_nondet_init` below, but instead of allocating and
/// non-deterministically initializing the the argument `expr` passed to that
/// function, we create a static global object of type \p type and
/// non-deterministically initialize it.
///
/// See gen_nondet_init for a description of the parameters.
/// The only new one is \p type, which is the type of the object to create.
///
/// \return The object created, the \p symbol_table gains any new symbols
///   created, and \p init_code gains any instructions required to initialize
///   either the returned value or its child objects
exprt object_factory(
  const typet &type,
  const irep_idt base_name,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  java_object_factory_parameterst parameters,
  lifetimet lifetime,
  const source_locationt &loc,
  const select_pointer_typet &pointer_type_selector)
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
  parameters.function_id = goto_functionst::entry_point();

  exprt object=main_symbol.symbol_expr();

  symbolt *main_symbol_ptr;
  bool moving_symbol_failed=symbol_table.move(main_symbol, main_symbol_ptr);
  CHECK_RETURN(!moving_symbol_failed);

  java_object_factoryt state(
    loc,
    parameters,
    symbol_table,
    pointer_type_selector);
  code_blockt assignments;
  state.gen_nondet_init(
    assignments,
    object,
    false, // is_sub
    "",    // class_identifier
    false, // skip_classid
    lifetime,
    {}, // no override_type
    1,  // initial depth
    update_in_placet::NO_UPDATE_IN_PLACE,
    loc);

  state.add_created_symbol(main_symbol_ptr);
  state.declare_created_symbols(init_code);

  init_code.append(assignments);
  return object;
}

/// Initializes a primitive-typed or reference-typed object tree rooted at
/// `expr`, allocating child objects as necessary and nondet-initializing their
/// members, or if MAY_ or MUST_UPDATE_IN_PLACE is set, re-initializing
/// already-allocated objects.
///
/// \param expr:
///   Lvalue expression to initialize.
/// \param [out] init_code:
///   A code block where the initializing assignments will be appended to.
///   It gets an instruction sequence to initialize or reinitialize `expr` and
///   child objects it refers to.
/// \param symbol_table:
///   The symbol table, where new variables created as a result of emitting code
///   to \p init_code will be inserted to.  This includes any necessary
///   temporaries, and if `create_dyn_objs` is false, any allocated objects.
/// \param loc:
///   Source location to which all generated code will be associated to.
/// \param skip_classid:
///   If true, skip initializing field `@class_identifier`.
/// \param lifetime:
///   Lifetime of the allocated objects (AUTOMATIC_LOCAL, STATIC_GLOBAL, or
///   DYNAMIC)
/// \param object_factory_parameters:
///   Parameters for the generation of non deterministic objects.
/// \param pointer_type_selector:
///   The pointer_selector to use to resolve pointer types where required.
/// \param update_in_place:
///   NO_UPDATE_IN_PLACE: initialize `expr` from scratch
///   MAY_UPDATE_IN_PLACE: generate a runtime nondet branch between the NO_
///   and MUST_ cases.
///   MUST_UPDATE_IN_PLACE: reinitialize an existing object
/// \return `init_code` gets an instruction sequence to initialize or
///   reinitialize `expr` and child objects it refers to. `symbol_table` is
///   modified with any new symbols created. This includes any necessary
///   temporaries, and if `create_dyn_objs` is false, any allocated objects.
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  bool skip_classid,
  lifetimet lifetime,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  update_in_placet update_in_place)
{
  java_object_factoryt state(
    loc,
    object_factory_parameters,
    symbol_table,
    pointer_type_selector);
  code_blockt assignments;
  state.gen_nondet_init(
    assignments,
    expr,
    false, // is_sub
    "",    // class_identifier
    skip_classid,
    lifetime,
    {}, // no override_type
    1,  // initial depth
    update_in_place,
    loc);

  state.declare_created_symbols(init_code);

  init_code.append(assignments);
}

/// Call object_factory() above with a default (identity) pointer_type_selector
exprt object_factory(
  const typet &type,
  const irep_idt base_name,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const java_object_factory_parameterst &object_factory_parameters,
  lifetimet lifetime,
  const source_locationt &location)
{
  select_pointer_typet pointer_type_selector;
  return object_factory(
    type,
    base_name,
    init_code,
    symbol_table,
    object_factory_parameters,
    lifetime,
    location,
    pointer_type_selector);
}

/// Call gen_nondet_init() above with a default (identity) pointer_type_selector
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  const source_locationt &loc,
  bool skip_classid,
  lifetimet lifetime,
  const java_object_factory_parameterst &object_factory_parameters,
  update_in_placet update_in_place)
{
  select_pointer_typet pointer_type_selector;
  gen_nondet_init(
    expr,
    init_code,
    symbol_table,
    loc,
    skip_classid,
    lifetime,
    object_factory_parameters,
    pointer_type_selector,
    update_in_place);
}

/// Adds a call for the given method to the end of `assignments` if the method
/// exists in the symbol table. Does nothing if the method does not exist.
/// \param assignments: A code block that the method call will be appended to.
/// \param instance_expr: The instance to call the method on. This argument is
///   ignored if the method is static.
/// \param method_name: The name of the method to be called.
void java_object_factoryt::gen_method_call_if_present(
  code_blockt &assignments,
  const exprt &instance_expr,
  const irep_idt &method_name)
{
  if(const auto func = symbol_table.lookup(method_name))
  {
    const java_method_typet &type = to_java_method_type(func->type);
    code_function_callt fun_call(func->symbol_expr());
    if(type.has_this())
      fun_call.arguments().push_back(address_of_exprt(instance_expr));
    assignments.add(fun_call);
  }
}
