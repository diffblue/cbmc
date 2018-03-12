/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#include "c_nondet_symbol_factory.h"

#include <set>
#include <sstream>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <linking/zero_initializer.h>

#include <goto-programs/goto_functions.h>

/// Create a new temporary static symbol
/// \param symbol_table: The symbol table to create the symbol in
/// \param loc: The location to assign to the symbol
/// \param type: The type of symbol to create
/// \param static_lifetime: Whether the symbol should have a static lifetime
/// \param prefix: The prefix to use for the symbol's basename
/// \return Returns a reference to the new symbol
static const symbolt &c_new_tmp_symbol(
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  const typet &type,
  const bool static_lifetime,
  const std::string &prefix="tmp")
{
  symbolt &tmp_symbol=
    get_fresh_aux_symbol(type, "", prefix, loc, ID_C, symbol_table);
  tmp_symbol.is_static_lifetime=static_lifetime;

  return tmp_symbol;
}

/// \param type: Desired type (C_bool or plain bool)
/// \return nondet expr of that type
static exprt c_get_nondet_bool(const typet &type)
{
  // We force this to 0 and 1 and won't consider other values
  return typecast_exprt(side_effect_expr_nondett(bool_typet()), type);
}

class symbol_factoryt
{
  std::vector<const symbolt *> &symbols_created;
  symbol_tablet &symbol_table;
  const source_locationt &loc;
  const bool assume_non_null;
  namespacet ns;

public:
  symbol_factoryt(
    std::vector<const symbolt *> &_symbols_created,
    symbol_tablet &_symbol_table,
    const source_locationt &loc,
    const bool _assume_non_null):
      symbols_created(_symbols_created),
      symbol_table(_symbol_table),
      loc(loc),
      assume_non_null(_assume_non_null),
      ns(_symbol_table)
  {}

  exprt allocate_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const bool static_lifetime);

  void gen_nondet_init(code_blockt &assignments, const exprt &expr);
};

/// Create a symbol for a pointer to point to
/// \param assignments: The code block to add code to
/// \param target_expr: The expression which we are allocating a symbol for
/// \param allocate_type: The type to use for the symbol. If this doesn't match
///   target_expr then a cast will be used for the assignment
/// \param static_lifetime: Whether the symbol created should have static
///   lifetime
/// \return Returns the address of the allocated symbol
exprt symbol_factoryt::allocate_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const bool static_lifetime)
{
  const symbolt &aux_symbol=
    c_new_tmp_symbol(
      symbol_table,
      loc,
      allocate_type,
      static_lifetime);
  symbols_created.push_back(&aux_symbol);

  const typet &allocate_type_resolved=ns.follow(allocate_type);
  const typet &target_type=ns.follow(target_expr.type().subtype());
  bool cast_needed=allocate_type_resolved!=target_type;

  exprt aoe=address_of_exprt(aux_symbol.symbol_expr());
  if(cast_needed)
  {
    aoe=typecast_exprt(aoe, target_expr.type());
  }

  // Add the following code to assignments:
  //   <target_expr> = &tmp$<temporary_counter>
  code_assignt assign(target_expr, aoe);
  assign.add_source_location()=loc;
  assignments.move(assign);

  return aoe;
}

/// Creates a nondet for expr, including calling itself recursively to make
/// appropriate symbols to point to if expr is a pointer.
/// \param assignments: The code block to add code to
/// \param expr: The expression which we are generating a non-determinate value
///   for
void symbol_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    code_blockt non_null_inst;

    exprt allocated=allocate_object(non_null_inst, expr, subtype, false);

    exprt init_expr;
    if(allocated.id()==ID_address_of)
    {
      init_expr=allocated.op0();
    }
    else
    {
      init_expr=dereference_exprt(allocated, allocated.type().subtype());
    }
    gen_nondet_init(non_null_inst, init_expr);

    if(assume_non_null)
    {
      // Add the following code to assignments:
      // <expr> = <aoe>;
      assignments.append(non_null_inst);
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
      auto set_null_inst=code_assignt(expr, null_pointer_exprt(pointer_type));
      set_null_inst.add_source_location()=loc;

      code_ifthenelset null_check;
      null_check.cond()=side_effect_expr_nondett(bool_typet());
      null_check.then_case()=set_null_inst;
      null_check.else_case()=non_null_inst;

      assignments.move(null_check);
    }
  }
  // TODO(OJones): Add support for structs and arrays
  else
  {
    // If type is a ID_c_bool then add the following code to assignments:
    //   <expr> = NONDET(_BOOL);
    // Else add the following code to assignments:
    //   <expr> = NONDET(type);
    exprt rhs=type.id()==ID_c_bool?
      c_get_nondet_bool(type):
      side_effect_expr_nondett(type);
    code_assignt assign(expr, rhs);
    assign.add_source_location()=loc;

    assignments.move(assign);
  }
}

/// Creates a symbol and generates code so that it can vary over all possible
/// values for its type. For pointers this involves allocating symbols which it
/// can point to.
/// \param init_code: The code block to add generated code to
/// \param symbol_table: The symbol table
/// \param base_name: The name to use for the symbol created
/// \param type: The type for the symbol created
/// \param loc: The location to assign to generated code
/// \param allow_null: Whether to allow a null value when type is a pointer
/// \return Returns the symbol_exprt for the symbol created
exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &loc,
  bool allow_null)
{
  irep_idt identifier=id2string(goto_functionst::entry_point())+
    "::"+id2string(base_name);

  auxiliary_symbolt main_symbol;
  main_symbol.mode=ID_C;
  main_symbol.is_static_lifetime=false;
  main_symbol.name=identifier;
  main_symbol.base_name=base_name;
  main_symbol.type=type;
  main_symbol.location=loc;

  symbol_exprt main_symbol_expr=main_symbol.symbol_expr();

  symbolt *main_symbol_ptr;
  bool moving_symbol_failed=symbol_table.move(main_symbol, main_symbol_ptr);
  CHECK_RETURN(!moving_symbol_failed);

  std::vector<const symbolt *> symbols_created;
  symbols_created.push_back(main_symbol_ptr);

  symbol_factoryt state(
    symbols_created,
    symbol_table,
    loc,
    !allow_null);
  code_blockt assignments;
  state.gen_nondet_init(assignments, main_symbol_expr);

  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt * const symbol_ptr : symbols_created)
  {
    code_declt decl(symbol_ptr->symbol_expr());
    decl.add_source_location()=loc;
    init_code.move(decl);
  }

  init_code.append(assignments);

  // Add the following code to init_code for each symbol that's been created:
  //   INPUT("<identifier>", <identifier>);
  for(symbolt const *symbol_ptr : symbols_created)
  {
    codet input_code(ID_input);
    input_code.operands().resize(2);
    input_code.op0()=
      address_of_exprt(index_exprt(
        string_constantt(symbol_ptr->base_name),
        from_integer(0, index_type())));
    input_code.op1()=symbol_ptr->symbol_expr();
    input_code.add_source_location()=loc;
    init_code.move(input_code);
  }

  return main_symbol_expr;
}
