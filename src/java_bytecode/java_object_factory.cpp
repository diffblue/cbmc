/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <unordered_set>
#include <sstream>

#include <util/arith_tools.h>
#include <util/fresh_symbol.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/namespace.h>
#include <util/nondet_bool.h>
#include <util/nondet_ifthenelse.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>

#include <linking/zero_initializer.h>

#include "java_object_factory.h"
#include "java_types.h"
#include "java_utils.h"

/*******************************************************************\

Function: new_tmp_symbol

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  code_blockt &init_code;
  std::unordered_set<irep_idt, irep_id_hash> recursion_set;
  bool assume_non_null;
  size_t max_nondet_array_length;
  symbol_tablet &symbol_table;
  namespacet ns;

  void set_null(
    const exprt &expr,
    const pointer_typet &ptr_type,
    const source_locationt &);

  void gen_pointer_target_init(
    const exprt &expr,
    const typet &target_type,
    bool create_dynamic_objects,
    const source_locationt &);

public:
  java_object_factoryt(
    code_blockt &_init_code,
    bool _assume_non_null,
    size_t _max_nondet_array_length,
    symbol_tablet &_symbol_table):
      init_code(_init_code),
      assume_non_null(_assume_non_null),
      max_nondet_array_length(_max_nondet_array_length),
      symbol_table(_symbol_table),
      ns(_symbol_table)
  {}

  exprt allocate_object(
    const exprt &,
    const typet &,
    const source_locationt &,
    bool create_dynamic_objects);

  void gen_nondet_array_init(const exprt &expr, const source_locationt &);

  void gen_nondet_init(
    const exprt &expr,
    bool is_sub,
    irep_idt class_identifier,
    const source_locationt &loc,
    bool create_dynamic_objects,
    bool override=false,
    const typet &override_type=empty_typet());
};

/*******************************************************************\

Function: java_object_factoryt::allocate_object

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt java_object_factoryt::allocate_object(
  const exprt &target_expr,
  const typet &allocate_type,
  const source_locationt &loc,
  bool create_dynamic_objects)
{
  const typet &allocate_type_resolved=ns.follow(allocate_type);
  const typet &target_type=ns.follow(target_expr.type().subtype());
  bool cast_needed=allocate_type_resolved!=target_type;
  if(!create_dynamic_objects)
  {
    symbolt &aux_symbol=new_tmp_symbol(symbol_table, loc, allocate_type);
    aux_symbol.is_static_lifetime=true;

    exprt object=aux_symbol.symbol_expr();
    exprt aoe=address_of_exprt(object);
    if(cast_needed)
      aoe=typecast_exprt(aoe, target_expr.type());
    code_assignt code(target_expr, aoe);
    code.add_source_location()=loc;
    init_code.copy_to_operands(code);
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
      code_assignt assign=code_assignt(malloc_sym.symbol_expr(), malloc_expr);
      code_assignt &malloc_assign=assign;
      malloc_assign.add_source_location()=loc;
      init_code.copy_to_operands(malloc_assign);
      malloc_expr=malloc_sym.symbol_expr();
      if(cast_needed)
        malloc_expr=typecast_exprt(malloc_expr, target_expr.type());
      code_assignt code(target_expr, malloc_expr);
      code.add_source_location()=loc;
      init_code.copy_to_operands(code);
      return malloc_sym.symbol_expr();
    }
    else
    {
      // make null
      null_pointer_exprt null_pointer_expr(to_pointer_type(target_expr.type()));
      code_assignt code(target_expr, null_pointer_expr);
      code.add_source_location()=loc;
      init_code.copy_to_operands(code);
      return exprt();
    }
  }
}

/*******************************************************************\

Function: java_object_factoryt::set_null

  Inputs: `expr`: pointer-typed lvalue expression to initialise
          `ptr_type`: pointer type to write

 Outputs:

 Purpose: Adds an instruction to `init_code` null-initialising
          `expr`.

\*******************************************************************/

void java_object_factoryt::set_null(
  const exprt &expr,
  const pointer_typet &ptr_type,
  const source_locationt &loc)
{
  null_pointer_exprt null_pointer_expr(ptr_type);
  code_assignt code(expr, null_pointer_expr);
  code.add_source_location()=loc;
  init_code.move_to_operands(code);
}

/*******************************************************************\

Function: java_object_factoryt::gen_pointer_target_init

  Inputs: `expr`: pointer-typed lvalue expression to initialise
          `target_type`: structure type to initialise, which may
            not match *expr (for example, expr might be void*)
          `create_dynamic_objects`: if true, use malloc to allocate
            objects; otherwise generate fresh static symbols.

 Outputs:

 Purpose: Initialises an object tree rooted at `expr`, allocating
          child objects as necessary and nondet-initialising their
          members.

\*******************************************************************/

void java_object_factoryt::gen_pointer_target_init(
  const exprt &expr,
  const typet &target_type,
  bool create_dynamic_objects,
  const source_locationt &loc)
{
  if(target_type.id()==ID_struct &&
     has_prefix(
       id2string(to_struct_type(target_type).get_tag()),
       "java::array["))
  {
    gen_nondet_array_init(expr, loc);
  }
  else
  {
    exprt target=
      allocate_object(
        expr,
        target_type,
        loc,
        create_dynamic_objects);
    exprt init_expr;
    if(target.id()==ID_address_of)
      init_expr=target.op0();
    else
      init_expr=
        dereference_exprt(target, target.type().subtype());
    gen_nondet_init(
      init_expr,
      false,
      "",
      loc,
      create_dynamic_objects,
      false,
      typet());
  }
}

/*******************************************************************\

Function: java_object_factoryt::gen_nondet_init

 Inputs:
  expr -
  is_sub -
  class_identifier -
  loc -
  create_dynamic_objects -
  override - Ignore the LHS' real type. Used at the moment for
             reference arrays, which are implemented as void*
             arrays but should be init'd as their true type with
             appropriate casts.
  override_type - Type to use if ignoring the LHS' real type

 Outputs:

 Purpose:

\*******************************************************************/

void java_object_factoryt::gen_nondet_init(
  const exprt &expr,
  bool is_sub,
  irep_idt class_identifier,
  const source_locationt &loc,
  bool create_dynamic_objects,
  bool override,
  const typet &override_type)
{
  const typet &type=
    override ? ns.follow(override_type) : ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    if(subtype.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(subtype);
      const irep_idt struct_tag=struct_type.get_tag();
      // set to null if found in recursion set and not a sub-type
      if(recursion_set.find(struct_tag)!=recursion_set.end() &&
         struct_tag==class_identifier)
      {
        set_null(expr, pointer_type, loc);
        return;
      }
    }

    nondet_ifthenelset init_null_diamond(
      init_code,
      symbol_table,
      loc,
      ID_java,
      "nondet_ptr_is_null");

    if(!assume_non_null)
    {
      init_null_diamond.begin_if();
      set_null(expr, pointer_type, loc);
      init_null_diamond.begin_else();
    }

    gen_pointer_target_init(
      expr,
      subtype,
      create_dynamic_objects,
      loc);

    if(!assume_non_null)
      init_null_diamond.finish();
  }
  else if(type.id()==ID_struct)
  {
    typedef struct_typet::componentst componentst;

    const struct_typet &struct_type=to_struct_type(type);
    const irep_idt struct_tag=struct_type.get_tag();

    const componentst &components=struct_type.components();

    if(!is_sub)
      class_identifier=struct_tag;

    recursion_set.insert(struct_tag);
    assert(!recursion_set.empty());

    for(const auto &component : components)
    {
      const typet &component_type=component.type();
      irep_idt name=component.get_name();

      member_exprt me(expr, name, component_type);

      if(name=="@class_identifier")
      {
        irep_idt qualified_clsid="java::"+as_string(class_identifier);
        constant_exprt ci(qualified_clsid, string_typet());
        code_assignt code(me, ci);
        code.add_source_location()=loc;
        init_code.copy_to_operands(code);
      }
      else if(name=="@lock")
      {
        code_assignt code(me, from_integer(0, me.type()));
        code.add_source_location()=loc;
        init_code.copy_to_operands(code);
      }
      else
      {
        assert(!name.empty());

        bool _is_sub=name[0]=='@';
#if 0
        irep_idt _class_identifier=
          _is_sub?(class_identifier.empty()?struct_tag:class_identifier):"";
#endif

        gen_nondet_init(
          me,
          _is_sub,
          class_identifier,
          loc,
          create_dynamic_objects);
      }
    }
    recursion_set.erase(struct_tag);
  }
  else
  {
    side_effect_expr_nondett se=side_effect_expr_nondett(type);

    code_assignt code(expr, se);
    code.add_source_location()=loc;
    init_code.copy_to_operands(code);
  }
}

/*******************************************************************\

Function: java_object_factoryt::gen_nondet_array_init

 Inputs:

 Outputs:

 Purpose: create code to initialize a Java array with size
          `max_nondet_array_length`, loop over elements and initialize
          them

\*******************************************************************/

void java_object_factoryt::gen_nondet_array_init(
  const exprt &expr,
  const source_locationt &loc)
{
  assert(expr.type().id()==ID_pointer);
  const typet &type=ns.follow(expr.type().subtype());
  const struct_typet &struct_type=to_struct_type(type);
  assert(expr.type().subtype().id()==ID_symbol);
  const typet &element_type=
    static_cast<const typet &>(expr.type().subtype().find(ID_C_element_type));

  auto max_length_expr=from_integer(max_nondet_array_length, java_int_type());

  typet allocate_type;
  symbolt &length_sym=new_tmp_symbol(
    symbol_table,
    loc,
    java_int_type(),
    "nondet_array_length");
  const auto &length_sym_expr=length_sym.symbol_expr();

  // Initialize array with some undetermined length:
  gen_nondet_init(length_sym_expr, false, irep_idt(), loc, false);

  // Insert assumptions to bound its length:
  binary_relation_exprt
    assume1(length_sym_expr, ID_ge, from_integer(0, java_int_type()));
  binary_relation_exprt
    assume2(length_sym_expr, ID_le, max_length_expr);
  code_assumet assume_inst1(assume1);
  code_assumet assume_inst2(assume2);
  init_code.move_to_operands(assume_inst1);
  init_code.move_to_operands(assume_inst2);

  side_effect_exprt java_new_array(ID_java_new_array, expr.type());
  java_new_array.copy_to_operands(length_sym_expr);
  java_new_array.type().subtype().set(ID_C_element_type, element_type);
  codet assign=code_assignt(expr, java_new_array);
  assign.add_source_location()=loc;
  init_code.copy_to_operands(assign);

  exprt init_array_expr=
    member_exprt(
      dereference_exprt(expr, expr.type().subtype()),
      "data",
      struct_type.components()[2].type());
  if(init_array_expr.type()!=pointer_typet(element_type))
    init_array_expr=
      typecast_exprt(init_array_expr, pointer_typet(element_type));

  // Interpose a new symbol, as the goto-symex stage can't handle array indexing
  // via a cast.
  symbolt &array_init_symbol=new_tmp_symbol(
    symbol_table,
    loc,
    init_array_expr.type(),
    "array_data_init");
  const auto &array_init_symexpr=array_init_symbol.symbol_expr();
  codet data_assign=code_assignt(array_init_symexpr, init_array_expr);
  data_assign.add_source_location()=loc;
  init_code.copy_to_operands(data_assign);

  // Emit init loop for(array_init_iter=0; array_init_iter!=array.length;
  //                  ++array_init_iter) init(array[array_init_iter]);
  symbolt &counter=new_tmp_symbol(
    symbol_table,
    loc,
    length_sym_expr.type(),
    "array_init_iter");
  exprt counter_expr=counter.symbol_expr();

  exprt java_zero=from_integer(0, java_int_type());
  init_code.copy_to_operands(code_assignt(counter_expr, java_zero));

  std::string head_name=as_string(counter.base_name)+"_header";
  code_labelt init_head_label(head_name, code_skipt());
  code_gotot goto_head(head_name);

  init_code.move_to_operands(init_head_label);

  std::string done_name=as_string(counter.base_name)+"_done";
  code_labelt init_done_label(done_name, code_skipt());
  code_gotot goto_done(done_name);

  code_ifthenelset done_test;
  done_test.cond()=equal_exprt(counter_expr, length_sym_expr);
  done_test.then_case()=goto_done;

  init_code.move_to_operands(done_test);

  // Add a redundant if(counter == max_length) break that is easier for the
  // unwinder to understand.
  code_ifthenelset max_test;
  max_test.cond()=equal_exprt(counter_expr, max_length_expr);
  max_test.then_case()=goto_done;

  init_code.move_to_operands(max_test);

  exprt arraycellref=dereference_exprt(
    plus_exprt(array_init_symexpr, counter_expr, array_init_symexpr.type()),
    array_init_symexpr.type().subtype());

  gen_nondet_init(
    arraycellref,
    false,
    irep_idt(),
    loc,
    true,
    true,
    element_type);

  exprt java_one=from_integer(1, java_int_type());
  code_assignt incr(counter_expr, plus_exprt(counter_expr, java_one));

  init_code.move_to_operands(incr);
  init_code.move_to_operands(goto_head);
  init_code.move_to_operands(init_done_label);
}

/*******************************************************************\

Function: object_factory

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt object_factory(
  const typet &type,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table,
  size_t max_nondet_array_length,
  const source_locationt &loc)
{
  if(type.id()==ID_pointer)
  {
    symbolt &aux_symbol=new_tmp_symbol(
      symbol_table,
      loc,
      type);
    aux_symbol.is_static_lifetime=true;

    exprt object=aux_symbol.symbol_expr();

    java_object_factoryt state(
      init_code,
      !allow_null,
      max_nondet_array_length,
      symbol_table);
    state.gen_nondet_init(
      object,
      false,
      "",
      loc,
      false);

    return object;
  }
  else if(type.id()==ID_c_bool)
  {
    // We force this to 0 and 1 and won't consider
    // other values.
    return get_nondet_bool(type);
  }
  else
    return side_effect_expr_nondett(type);
}
