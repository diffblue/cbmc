/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/expr_util.h>
#include <util/message.h>
#include <util/arith_tools.h>
#include <util/cprover_prefix.h>
#include <util/std_types.h>
#include <util/pointer_offset_size.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/string2int.h>
#include <util/invariant_utils.h>
#include <util/c_types.h>

#include <linking/zero_initializer.h>

#include "goto_symex_state.h"

inline static typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil())
        return t;
    }
  }

  return nil_typet();
}

void goto_symext::symex_allocate(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=2)
    throw "allocate expected to have two operands";

  if(lhs.is_nil())
    return; // ignore

  dynamic_counter++;

  exprt size=code.op0();
  typet object_type=nil_typet();
  auto function_symbol = outer_symbol_table.lookup(state.source.pc->function);
  INVARIANT(function_symbol, "function associated with instruction not found");
  const irep_idt &mode = function_symbol->mode;

  // is the type given?
  if(code.type().id()==ID_pointer && code.type().subtype().id()!=ID_empty)
  {
    object_type=code.type().subtype();
  }
  else
  {
    exprt tmp_size=size;
    state.rename(tmp_size, ns); // to allow constant propagation
    simplify(tmp_size, ns);

    // special treatment for sizeof(T)*x
    {
      typet tmp_type=c_sizeof_type_rec(tmp_size);

      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(tmp_type, ns);
        mp_integer alloc_size;

        if(elem_size<0)
        {
        }
        else if(to_integer(tmp_size, alloc_size) &&
                tmp_size.id()==ID_mult &&
                tmp_size.operands().size()==2 &&
                (tmp_size.op0().is_constant() ||
                 tmp_size.op1().is_constant()))
        {
          exprt s=tmp_size.op0();
          if(s.is_constant())
          {
            s=tmp_size.op1();
            PRECONDITION(c_sizeof_type_rec(tmp_size.op0()) == tmp_type);
          }
          else
            PRECONDITION(c_sizeof_type_rec(tmp_size.op1()) == tmp_type);

          object_type=array_typet(tmp_type, s);
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;

            if(elements*elem_size==alloc_size)
              object_type=array_typet(
                tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }

    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), tmp_size);

    // we introduce a fresh symbol for the size
    // to prevent any issues of the size getting ever changed

    if(object_type.id()==ID_array &&
       !to_array_type(object_type).size().is_constant())
    {
      exprt &size=to_array_type(object_type).size();

      symbolt size_symbol;

      size_symbol.base_name=
        "dynamic_object_size"+std::to_string(dynamic_counter);
      size_symbol.name="symex_dynamic::"+id2string(size_symbol.base_name);
      size_symbol.is_lvalue=true;
      size_symbol.type=tmp_size.type();
      size_symbol.mode = mode;

      state.symbol_table.add(size_symbol);

      code_assignt assignment(size_symbol.symbol_expr(), size);
      size=assignment.lhs();

      symex_assign(state, assignment);
    }
  }

  // value
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+std::to_string(dynamic_counter);
  value_symbol.name="symex_dynamic::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=object_type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode = mode;

  state.symbol_table.add(value_symbol);

  exprt zero_init=code.op1();
  state.rename(zero_init, ns); // to allow constant propagation
  simplify(zero_init, ns);

  if(!zero_init.is_constant())
    throw "allocate expects constant as second argument";

  if(!zero_init.is_zero() && !zero_init.is_false())
  {
    null_message_handlert null_message;
    exprt zero_value=
      zero_initializer(
        object_type,
        code.source_location(),
        ns,
        null_message);

    if(zero_value.is_not_nil())
    {
      code_assignt assignment(value_symbol.symbol_expr(), zero_value);
      symex_assign(state, assignment);
    }
    else
      throw "failed to zero initialize dynamic object";
  }

  exprt rhs;

  if(object_type.id()==ID_array)
  {
    index_exprt index_expr(value_symbol.type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=from_integer(0, index_type());
    rhs=address_of_exprt(
      index_expr, pointer_type(value_symbol.type.subtype()));
  }
  else
  {
    rhs=address_of_exprt(
      value_symbol.symbol_expr(), pointer_type(value_symbol.type));
  }

  if(rhs.type()!=lhs.type())
    rhs.make_typecast(lhs.type());

  symex_assign(state, code_assignt(lhs, rhs));
}

irep_idt get_symbol(const exprt &src)
{
  if(src.id()==ID_typecast)
    return get_symbol(to_typecast_expr(src).op());
  else if(src.id()==ID_address_of)
  {
    exprt op=to_address_of_expr(src).object();
    if(op.id()==ID_symbol &&
       op.get_bool(ID_C_SSA_symbol))
      return to_ssa_expr(op).get_object_name();
    else
      return irep_idt();
  }
  else
    return irep_idt();
}

void goto_symext::symex_gcc_builtin_va_arg_next(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw "va_arg_next expected to have one operand";

  if(lhs.is_nil())
    return; // ignore

  exprt tmp=code.op0();
  state.rename(tmp, ns); // to allow constant propagation
  do_simplify(tmp);
  irep_idt id=get_symbol(tmp);

  exprt rhs=zero_initializer(lhs.type(), code.source_location(), ns);

  if(!id.empty())
  {
    // strip last name off id to get function name
    std::size_t pos=id2string(id).rfind("::");
    if(pos!=std::string::npos)
    {
      irep_idt function_identifier=std::string(id2string(id), 0, pos);
      std::string base=id2string(function_identifier)+"::va_arg";

      if(has_prefix(id2string(id), base))
        id=base+std::to_string(
          safe_string2unsigned(
            std::string(id2string(id), base.size(), std::string::npos))+1);
      else
        id=base+"0";

      const symbolt *symbol;
      if(!ns.lookup(id, symbol))
      {
        const symbol_exprt symbol_expr(symbol->name, symbol->type);
        rhs=address_of_exprt(symbol_expr);
        rhs.make_typecast(lhs.type());
      }
    }
  }

  symex_assign(state, code_assignt(lhs, rhs));
}

irep_idt get_string_argument_rec(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    PRECONDITION(src.operands().size() == 1);
    return get_string_argument_rec(src.op0());
  }
  else if(src.id()==ID_address_of)
  {
    PRECONDITION(src.operands().size() == 1);
    if(src.op0().id()==ID_index)
    {
      PRECONDITION(src.op0().operands().size() == 2);

      if(src.op0().op0().id()==ID_string_constant &&
         src.op0().op1().is_zero())
      {
        const exprt &fmt_str=src.op0().op0();
        return fmt_str.get_string(ID_value);
      }
    }
  }

  return "";
}

irep_idt get_string_argument(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  simplify(tmp, ns);
  return get_string_argument_rec(tmp);
}

void goto_symext::symex_printf(
  statet &state,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.operands().empty())
    throw "printf expected to have at least one operand";

  exprt tmp_rhs=rhs;
  state.rename(tmp_rhs, ns);
  do_simplify(tmp_rhs);

  const exprt::operandst &operands=tmp_rhs.operands();
  std::list<exprt> args;

  for(std::size_t i=1; i<operands.size(); i++)
    args.push_back(operands[i]);

  const irep_idt format_string=
    get_string_argument(operands[0], ns);

  if(format_string!="")
    target.output_fmt(
      state.guard.as_expr(),
      state.source, "printf", format_string, args);
}

void goto_symext::symex_input(
  statet &state,
  const codet &code)
{
  if(code.operands().size()<2)
    throw "input expected to have at least two operands";

  exprt id_arg=code.op0();

  state.rename(id_arg, ns);

  std::list<exprt> args;

  for(std::size_t i=1; i<code.operands().size(); i++)
  {
    args.push_back(code.operands()[i]);
    state.rename(args.back(), ns);
    do_simplify(args.back());
  }

  const irep_idt input_id=get_string_argument(id_arg, ns);

  target.input(state.guard.as_expr(), state.source, input_id, args);
}

void goto_symext::symex_output(
  statet &state,
  const codet &code)
{
  if(code.operands().size()<2)
    throw "output expected to have at least two operands";

  exprt id_arg=code.op0();

  state.rename(id_arg, ns);

  std::list<exprt> args;

  for(std::size_t i=1; i<code.operands().size(); i++)
  {
    args.push_back(code.operands()[i]);
    state.rename(args.back(), ns);
    do_simplify(args.back());
  }

  const irep_idt output_id=get_string_argument(id_arg, ns);

  target.output(state.guard.as_expr(), state.source, output_id, args);
}

/// Handles side effects of type 'new' for C++ and 'new array'
/// for C++ and Java language modes
/// \param state: Symex state
/// \param lhs: left-hand side of assignment
/// \param code: right-hand side containing side effect
void goto_symext::symex_cpp_new(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  bool do_array;

  if(code.type().id()!=ID_pointer)
    throw "new expected to return pointer";
  do_array =
    (code.get(ID_statement) == ID_cpp_new_array ||
     code.get(ID_statement) == ID_java_new_array_data);

  dynamic_counter++;

  const std::string count_string(std::to_string(dynamic_counter));

  // value
  symbolt symbol;
  symbol.base_name=
    do_array?"dynamic_"+count_string+"_array":
             "dynamic_"+count_string+"_value";
  symbol.name="symex_dynamic::"+id2string(symbol.base_name);
  symbol.is_lvalue=true;
  if(code.get(ID_statement)==ID_cpp_new_array ||
     code.get(ID_statement)==ID_cpp_new)
    symbol.mode=ID_cpp;
  else if(code.get(ID_statement) == ID_java_new_array_data)
    symbol.mode=ID_java;
  else
    INVARIANT_WITH_IREP(false, "Unexpected side effect expression", code);

  if(do_array)
  {
    exprt size_arg = static_cast<const exprt &>(code.find(ID_size));
    clean_expr(size_arg, state, false);
    symbol.type = array_typet(code.type().subtype(), size_arg);
  }
  else
    symbol.type=code.type().subtype();

  symbol.type.set("#dynamic", true);

  state.symbol_table.add(symbol);

  // make symbol expression

  exprt rhs(ID_address_of, code.type());
  rhs.type().subtype()=code.type().subtype();

  if(do_array)
  {
    index_exprt index_expr(symbol.symbol_expr(), from_integer(0, index_type()));
    rhs.move_to_operands(index_expr);
  }
  else
    rhs.copy_to_operands(symbol.symbol_expr());

  symex_assign(state, code_assignt(lhs, rhs));
}

void goto_symext::symex_cpp_delete(
  statet &state,
  const codet &code)
{
  // TODO
  #if 0
  bool do_array=code.get(ID_statement)==ID_cpp_delete_array;
  #endif
}

void goto_symext::symex_trace(
  statet &state,
  const code_function_callt &code)
{
  if(code.arguments().size()<2)
    // NOLINTNEXTLINE(readability/throw)
    throw "symex_trace expects at least two arguments";

  int debug_thresh=unsafe_string2int(options.get_option("debug-level"));

  mp_integer debug_lvl;

  if(to_integer(code.arguments()[0], debug_lvl))
    // NOLINTNEXTLINE(readability/throw)
    throw "CBMC_trace expects constant as first argument";

  if(code.arguments()[1].id()!="implicit_address_of" ||
     code.arguments()[1].operands().size()!=1 ||
     code.arguments()[1].op0().id()!=ID_string_constant)
    // NOLINTNEXTLINE(readability/throw)
    throw "CBMC_trace expects string constant as second argument";

  if(mp_integer(debug_thresh)>=debug_lvl)
  {
    std::list<exprt> vars;

    irep_idt event=code.arguments()[1].op0().get(ID_value);

    for(std::size_t j=2; j<code.arguments().size(); j++)
    {
      exprt var(code.arguments()[j]);
      state.rename(var, ns);
      vars.push_back(var);
    }

    target.output(state.guard.as_expr(), state.source, event, vars);
  }
}

void goto_symext::symex_fkt(
  statet &state,
  const code_function_callt &code)
{
  #if 0
  exprt new_fc(ID_function, fc.type());

  new_fc.reserve_operands(fc.operands().size()-1);

  bool first=true;

  Forall_operands(it, fc)
    if(first)
      first=false;
    else
      new_fc.move_to_operands(*it);

  new_fc.set(ID_identifier, fc.op0().get(ID_identifier));

  fc.swap(new_fc);
  #endif
}

void goto_symext::symex_macro(
  statet &state,
  const code_function_callt &code)
{
  const irep_idt &identifier=code.op0().get(ID_identifier);

  if(identifier==CPROVER_MACRO_PREFIX "waitfor")
  {
    #if 0
    exprt new_fc("waitfor", fc.type());

    if(fc.operands().size()!=4)
      throw "waitfor expected to have four operands";

    exprt &cycle_var=fc.op1();
    exprt &bound=fc.op2();
    exprt &predicate=fc.op3();

    if(cycle_var.id()!=ID_symbol)
      throw "waitfor expects symbol as first operand but got "+
            cycle_var.id();

    exprt new_cycle_var(cycle_var);
    new_cycle_var.id("waitfor_symbol");
    new_cycle_var.copy_to_operands(bound);

    replace_expr(cycle_var, new_cycle_var, predicate);

    new_fc.operands().resize(4);
    new_fc.op0().swap(cycle_var);
    new_fc.op1().swap(new_cycle_var);
    new_fc.op2().swap(bound);
    new_fc.op3().swap(predicate);

    fc.swap(new_fc);
    #endif
  }
  else
    throw "unknown macro: "+id2string(identifier);
}
