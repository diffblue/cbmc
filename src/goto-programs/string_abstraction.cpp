/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#include "string_abstraction.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/pointer_predicates.h>
#include <util/string_constant.h>
#include <util/type_eq.h>

#include "pointer_arithmetic.h"

bool string_abstractiont::build_wrap(
  const exprt &object,
  exprt &dest, bool write)
{
  // debugging
  if(build(object, dest, write))
    return true;

  // extra consistency check
  // use
  // #define build_wrap(a,b,c) build(a,b,c)
  // to avoid it
  const typet &a_t=build_abstraction_type(object.type());
  /*assert(type_eq(dest.type(), a_t, ns) ||
      (dest.type().id()==ID_array && a_t.id()==ID_pointer &&
       type_eq(dest.type().subtype(), a_t.subtype(), ns)));
       */
  if(!type_eq(dest.type(), a_t, ns) &&
      !(dest.type().id()==ID_array && a_t.id()==ID_pointer &&
       type_eq(dest.type().subtype(), a_t.subtype(), ns)))
  {
    warning() << "warning: inconsistent abstract type for "
              << object.pretty() << eom;
    return true;
  }

  return false;
}

bool string_abstractiont::is_ptr_string_struct(const typet &type) const
{
  return type.id()==ID_pointer &&
    type_eq(type.subtype(), string_struct, ns);
}

static inline bool is_ptr_argument(const typet &type)
{
  return type.id()==ID_pointer;
}

void string_abstraction(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  goto_programt &dest)
{
  string_abstractiont string_abstraction(symbol_table, message_handler);
  string_abstraction(dest);
}

void string_abstraction(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  goto_functionst &dest)
{
  string_abstractiont string_abstraction(symbol_table, message_handler);
  string_abstraction(dest);
}

void string_abstraction(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  string_abstraction(
    goto_model.symbol_table,
    message_handler,
    goto_model.goto_functions);
}

string_abstractiont::string_abstractiont(
  symbol_tablet &_symbol_table,
  message_handlert &_message_handler):
  messaget(_message_handler),
  arg_suffix("#strarg"),
  sym_suffix("#str$fcn"),
  symbol_table(_symbol_table),
  ns(_symbol_table),
  temporary_counter(0)
{
  struct_typet s;

  s.components().resize(3);

  s.components()[0].set_name("is_zero");
  s.components()[0].set_pretty_name("is_zero");
  s.components()[0].type()=build_type(whatt::IS_ZERO);

  s.components()[1].set_name("length");
  s.components()[1].set_pretty_name("length");
  s.components()[1].type()=build_type(whatt::LENGTH);

  s.components()[2].set_name("size");
  s.components()[2].set_pretty_name("size");
  s.components()[2].type()=build_type(whatt::SIZE);

  string_struct=s;
}

typet string_abstractiont::build_type(whatt what)
{
  typet type;

  switch(what)
  {
  case whatt::IS_ZERO: type=bool_typet(); break;
  case whatt::LENGTH:  type=size_type(); break;
  case whatt::SIZE:    type=size_type(); break;
  }

  return type;
}

void string_abstractiont::operator()(goto_functionst &dest)
{
  Forall_goto_functions(it, dest)
  {
    sym_suffix="#str$"+id2string(it->first);
    add_str_arguments(it->first, it->second);
    abstract(it->second.body);
    current_args.clear();
  }

  // do we have a main?
  goto_functionst::function_mapt::iterator
    m_it=dest.function_map.find(dest.entry_point());

  if(m_it!=dest.function_map.end())
  {
    goto_programt &main=m_it->second.body;

    // do initialization
    initialization.destructive_append(main);
    main.swap(initialization);
    initialization.clear();
  }
}

void string_abstractiont::operator()(goto_programt &dest)
{
  abstract(dest);

  // do initialization
  initialization.destructive_append(dest);
  dest.swap(initialization);
  initialization.clear();
}

void string_abstractiont::add_str_arguments(
    const irep_idt &name,
    goto_functionst::goto_functiont &fct)
{
  symbolt &fct_symbol=*symbol_table.get_writeable(name);

  code_typet::parameterst &parameters=
    to_code_type(fct.type).parameters();
  code_typet::parameterst str_args;

  for(code_typet::parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      ++it)
  {
    const typet &abstract_type=build_abstraction_type(it->type());
    if(abstract_type.is_nil())
      continue;

    const irep_idt &identifier=it->get_identifier();
    if(identifier=="")
      continue; // ignore

    add_argument(str_args, fct_symbol, abstract_type,
        id2string(it->get_base_name())+arg_suffix,
        id2string(identifier)+arg_suffix);

    current_args.insert(identifier);
  }

  parameters.insert(parameters.end(), str_args.begin(), str_args.end());
  code_typet::parameterst &symb_parameters=
    to_code_type(fct_symbol.type).parameters();
  symb_parameters.insert(
    symb_parameters.end(), str_args.begin(), str_args.end());
}

void string_abstractiont::add_argument(
    code_typet::parameterst &str_args,
    const symbolt &fct_symbol,
    const typet &type,
    const irep_idt &base_name,
    const irep_idt &identifier)
{
  typet final_type=is_ptr_argument(type)?
                   type:pointer_type(type);

  str_args.push_back(code_typet::parametert(final_type));
  str_args.back().add_source_location()=fct_symbol.location;
  str_args.back().set_base_name(base_name);
  str_args.back().set_identifier(identifier);

  auxiliary_symbolt new_symbol;
  new_symbol.type=final_type;
  new_symbol.value.make_nil();
  new_symbol.location=str_args.back().source_location();
  new_symbol.name=str_args.back().get_identifier();
  new_symbol.module=fct_symbol.module;
  new_symbol.base_name=str_args.back().get_base_name();
  new_symbol.mode=fct_symbol.mode;
  new_symbol.pretty_name=str_args.back().get_base_name();

  symbol_table.insert(std::move(new_symbol));
}

void string_abstractiont::abstract(goto_programt &dest)
{
  locals.clear();

  Forall_goto_program_instructions(it, dest)
    it=abstract(dest, it);

  if(locals.empty())
    return;

  // go over it again for the newly added locals
  declare_define_locals(dest);
  locals.clear();
}

void string_abstractiont::declare_define_locals(goto_programt &dest)
{
  typedef std::unordered_map<irep_idt, goto_programt::targett> available_declst;
  available_declst available_decls;

  Forall_goto_program_instructions(it, dest)
    if(it->is_decl())
      // same name may exist several times due to inlining, make sure the first
      // declaration is used
      available_decls.insert(std::make_pair(
            to_code_decl(it->code).get_identifier(), it));

  // declare (and, if necessary, define) locals
  for(const auto &l : locals)
  {
    goto_programt::targett ref_instr=dest.instructions.begin();
    bool has_decl=false;

    available_declst::const_iterator entry=available_decls.find(l.first);

    if(available_declst::const_iterator(available_decls.end())!=entry)
    {
      ref_instr=entry->second;
      has_decl=true;
    }

    goto_programt tmp;
    make_decl_and_def(tmp, ref_instr, l.second, l.first);

    if(has_decl)
      ++ref_instr;
    dest.insert_before_swap(ref_instr, tmp);
  }
}

void string_abstractiont::make_decl_and_def(goto_programt &dest,
    goto_programt::targett ref_instr,
    const irep_idt &identifier,
    const irep_idt &source_sym)
{
  const symbolt &symbol=ns.lookup(identifier);
  symbol_exprt sym_expr=symbol.symbol_expr();

  goto_programt::targett decl1=dest.add_instruction();
  decl1->make_decl();
  decl1->source_location=ref_instr->source_location;
  decl1->function=ref_instr->function;
  decl1->code=code_declt(sym_expr);
  decl1->code.add_source_location()=ref_instr->source_location;

  exprt val=symbol.value;
  // initialize pointers with suitable objects
  if(val.is_nil())
  {
    const symbolt &orig=ns.lookup(source_sym);
    val=make_val_or_dummy_rec(dest, ref_instr, symbol, ns.follow(orig.type));
  }

  // may still be nil (structs, then assignments have been done already)
  if(val.is_not_nil())
  {
    goto_programt::targett assignment1=dest.add_instruction();
    assignment1->make_assignment();
    assignment1->source_location=ref_instr->source_location;
    assignment1->function=ref_instr->function;
    assignment1->code=code_assignt(sym_expr, val);
    assignment1->code.add_source_location()=ref_instr->source_location;
  }
}

exprt string_abstractiont::make_val_or_dummy_rec(goto_programt &dest,
    goto_programt::targett ref_instr,
    const symbolt &symbol, const typet &source_type)
{
  const typet &eff_type=ns.follow(symbol.type);

  if(eff_type.id()==ID_array || eff_type.id()==ID_pointer)
  {
    const typet &source_subt=is_ptr_string_struct(eff_type)?
      source_type:ns.follow(source_type.subtype());
    symbol_exprt sym_expr=add_dummy_symbol_and_value(
        dest, ref_instr, symbol, irep_idt(),
        eff_type.subtype(), source_subt);

    if(eff_type.id()==ID_array)
      return array_of_exprt(sym_expr, to_array_type(eff_type));
    else
      return address_of_exprt(sym_expr);
  }
  else if(eff_type.id()==ID_union ||
      (eff_type.id()==ID_struct && !type_eq(eff_type, string_struct, ns)))
  {
    const struct_union_typet &su_source=to_struct_union_type(source_type);
    const struct_union_typet::componentst &s_components=
      su_source.components();
    const struct_union_typet &struct_union_type=to_struct_union_type(eff_type);
    const struct_union_typet::componentst &components=
      struct_union_type.components();
    unsigned seen=0;

    struct_union_typet::componentst::const_iterator it2=components.begin();
    for(struct_union_typet::componentst::const_iterator
        it=s_components.begin();
        it!=s_components.end() && it2!=components.end();
        ++it)
    {
      if(it->get_name()!=it2->get_name())
        continue;

      const typet &eff_sub_type=ns.follow(it2->type());
      if(eff_sub_type.id()==ID_pointer ||
          eff_sub_type.id()==ID_array ||
          eff_sub_type.id()==ID_struct ||
          eff_sub_type.id()==ID_union)
      {
        symbol_exprt sym_expr=add_dummy_symbol_and_value(
            dest, ref_instr, symbol, it2->get_name(),
            it2->type(), ns.follow(it->type()));

        member_exprt member(symbol.symbol_expr(), it2->get_name(), it2->type());

        goto_programt::targett assignment1=dest.add_instruction();
        assignment1->make_assignment();
        assignment1->source_location=ref_instr->source_location;
        assignment1->function=ref_instr->function;
        assignment1->code=code_assignt(member, sym_expr);
        assignment1->code.add_source_location()=ref_instr->source_location;
      }

      ++seen;
      ++it2;
    }

    INVARIANT(
      components.size() == seen,
      "some of the symbol's component names were not found in the source");
  }

  return nil_exprt();
}

symbol_exprt string_abstractiont::add_dummy_symbol_and_value(
    goto_programt &dest,
    goto_programt::targett ref_instr,
    const symbolt &symbol,
    const irep_idt &component_name,
    const typet &type,
    const typet &source_type)
{
  std::string suffix="$strdummy";
  if(!component_name.empty())
    suffix="#"+id2string(component_name)+suffix;

  irep_idt dummy_identifier=id2string(symbol.name)+suffix;

  auxiliary_symbolt new_symbol;
  new_symbol.type=type;
  new_symbol.value.make_nil();
  new_symbol.location=ref_instr->source_location;
  new_symbol.name=dummy_identifier;
  new_symbol.module=symbol.module;
  new_symbol.base_name=id2string(symbol.base_name)+suffix;
  new_symbol.mode=symbol.mode;
  new_symbol.pretty_name=id2string(
      symbol.pretty_name.empty()?symbol.base_name:symbol.pretty_name)+suffix;

  symbol_exprt sym_expr=new_symbol.symbol_expr();

  // make sure it is declared before the recursive call
  goto_programt::targett decl=dest.add_instruction();
  decl->make_decl();
  decl->source_location=ref_instr->source_location;
  decl->function=ref_instr->function;
  decl->code=code_declt(sym_expr);
  decl->code.add_source_location()=ref_instr->source_location;

  // set the value - may be nil
  if(source_type.id()==ID_array && is_char_type(source_type.subtype()) &&
      type_eq(type, string_struct, ns))
  {
    new_symbol.value=struct_exprt(string_struct);
    new_symbol.value.operands().resize(3);
    new_symbol.value.op0()=build_unknown(whatt::IS_ZERO, false);
    new_symbol.value.op1()=build_unknown(whatt::LENGTH, false);
    new_symbol.value.op2()=to_array_type(source_type).size().id()==ID_infinity?
      build_unknown(whatt::SIZE, false):to_array_type(source_type).size();
    make_type(new_symbol.value.op2(), build_type(whatt::SIZE));
  }
  else
    new_symbol.value=
      make_val_or_dummy_rec(dest, ref_instr, new_symbol, source_type);

  if(new_symbol.value.is_not_nil())
  {
    goto_programt::targett assignment1=dest.add_instruction();
    assignment1->make_assignment();
    assignment1->source_location=ref_instr->source_location;
    assignment1->function=ref_instr->function;
    assignment1->code=code_assignt(sym_expr, new_symbol.value);
    assignment1->code.add_source_location()=ref_instr->source_location;
  }

  symbol_table.insert(std::move(new_symbol));

  return sym_expr;
}

goto_programt::targett string_abstractiont::abstract(
  goto_programt &dest,
  goto_programt::targett it)
{
  switch(it->type)
  {
  case ASSIGN:
    it=abstract_assign(dest, it);
    break;

  case GOTO:
  case ASSERT:
  case ASSUME:
    if(has_string_macros(it->guard))
      replace_string_macros(it->guard, false, it->source_location);
    break;

  case FUNCTION_CALL:
    abstract_function_call(it);
    break;

  case RETURN:
    // use remove_returns
    UNREACHABLE;
    break;

  case END_FUNCTION:
  case START_THREAD:
  case END_THREAD:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case DECL:
  case DEAD:
  case CATCH:
  case THROW:
  case SKIP:
  case OTHER:
  case LOCATION:
    break;

  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    UNREACHABLE;
    break;
  }

  return it;
}

goto_programt::targett string_abstractiont::abstract_assign(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_assignt &assign=to_code_assign(target->code);

  exprt &lhs=assign.lhs();
  exprt &rhs=assign.rhs();

  if(has_string_macros(lhs))
  {
    replace_string_macros(lhs, true, target->source_location);
    move_lhs_arithmetic(lhs, rhs);
  }

  if(has_string_macros(rhs))
    replace_string_macros(rhs, false, target->source_location);

  const typet &type = lhs.type();
  if(type.id()==ID_pointer || type.id()==ID_array)
    return abstract_pointer_assign(dest, target);
  else if(is_char_type(type))
    return abstract_char_assign(dest, target);

  return target;
}

void string_abstractiont::abstract_function_call(
  goto_programt::targett target)
{
  code_function_callt &call=to_code_function_call(target->code);
  code_function_callt::argumentst &arguments=call.arguments();
  code_function_callt::argumentst str_args;

  const symbolt &fct_symbol=ns.lookup(call.function().get(ID_identifier));
  const code_typet::parameterst &formal_params=
    to_code_type(fct_symbol.type).parameters();

  code_function_callt::argumentst::const_iterator it1=arguments.begin();
  for(code_typet::parameterst::const_iterator it2=formal_params.begin();
      it2!=formal_params.end();
      it2++, it1++)
  {
    const typet &abstract_type=build_abstraction_type(it2->type());
    if(abstract_type.is_nil())
      continue;

    if(it1==arguments.end())
    {
      throw incorrect_goto_program_exceptiont(
        "function call: not enough arguments", target->source_location);
    }

    str_args.push_back(exprt());
    // if function takes void*, build for *it1 will fail if actual parameter
    // is of some other pointer type; then just introduce an unknown
    if(build_wrap(*it1, str_args.back(), false))
      str_args.back()=build_unknown(abstract_type, false);
    // array -> pointer translation
    if(str_args.back().type().id()==ID_array &&
        abstract_type.id()==ID_pointer)
    {
      INVARIANT(
        type_eq(str_args.back().type().subtype(), abstract_type.subtype(), ns),
        "argument array type differs from formal parameter pointer type");

      index_exprt idx(str_args.back(), from_integer(0, index_type()));
      // disable bounds check on that one
      idx.set("bounds_check", false);

      str_args.back()=address_of_exprt(idx);
    }

    if(!is_ptr_argument(abstract_type))
      str_args.back()=address_of_exprt(str_args.back());
  }

  arguments.insert(arguments.end(), str_args.begin(), str_args.end());
}

bool string_abstractiont::has_string_macros(const exprt &expr)
{
  if(expr.id()=="is_zero_string" ||
     expr.id()=="zero_string_length" ||
     expr.id()=="buffer_size")
    return true;

  forall_operands(it, expr)
    if(has_string_macros(*it))
      return true;

  return false;
}

void string_abstractiont::replace_string_macros(
  exprt &expr,
  bool lhs,
  const source_locationt &source_location)
{
  if(expr.id()=="is_zero_string")
  {
    PRECONDITION(expr.operands().size() == 1);
    exprt tmp=build(expr.op0(), whatt::IS_ZERO, lhs, source_location);
    expr.swap(tmp);
  }
  else if(expr.id()=="zero_string_length")
  {
    PRECONDITION(expr.operands().size() == 1);
    exprt tmp=build(expr.op0(), whatt::LENGTH, lhs, source_location);
    expr.swap(tmp);
  }
  else if(expr.id()=="buffer_size")
  {
    PRECONDITION(expr.operands().size() == 1);
    exprt tmp=build(expr.op0(), whatt::SIZE, false, source_location);
    expr.swap(tmp);
  }
  else
    Forall_operands(it, expr)
      replace_string_macros(*it, lhs, source_location);
}

exprt string_abstractiont::build(
  const exprt &pointer,
  whatt what,
  bool write,
  const source_locationt &source_location)
{
  // take care of pointer typecasts now
  if(pointer.id()==ID_typecast)
  {
    // cast from another pointer type?
    INVARIANT(
      pointer.operands().size() == 1,
      "pointer typecast takes exactly 1 argument");
    if(pointer.op0().type().id() != ID_pointer)
      return build_unknown(what, write);

    // recursive call
    return build(pointer.op0(), what, write, source_location);
  }

  exprt str_struct;
  if(build_wrap(pointer, str_struct, write))
    UNREACHABLE;

  exprt result=member(str_struct, what);

  if(what==whatt::LENGTH || what==whatt::SIZE)
  {
    // adjust for offset
    result=minus_exprt(result, pointer_offset(pointer));
    result.op0().make_typecast(result.op1().type());
  }

  return result;
}

const typet &string_abstractiont::build_abstraction_type(const typet &type)
{
  const typet &eff_type=ns.follow(type);
  abstraction_types_mapt::const_iterator map_entry=
    abstraction_types_map.find(eff_type);
  if(map_entry!=abstraction_types_map.end())
    return map_entry->second;

  abstraction_types_mapt tmp;
  tmp.swap(abstraction_types_map);
  build_abstraction_type_rec(eff_type, tmp);

  abstraction_types_map.swap(tmp);
  map_entry=tmp.find(eff_type);
  CHECK_RETURN(map_entry != tmp.end());
  return abstraction_types_map.insert(
      std::make_pair(eff_type, map_entry->second)).first->second;
}

const typet &string_abstractiont::build_abstraction_type_rec(const typet &type,
    const abstraction_types_mapt &known)
{
  const typet &eff_type=ns.follow(type);
  abstraction_types_mapt::const_iterator known_entry=known.find(eff_type);
  if(known_entry!=known.end())
    return known_entry->second;

  ::std::pair< abstraction_types_mapt::iterator, bool > map_entry(
      abstraction_types_map.insert(::std::make_pair(
          eff_type, nil_typet())));
  if(!map_entry.second)
    return map_entry.first->second;

  if(eff_type.id()==ID_array || eff_type.id()==ID_pointer)
  {
    // char* or void* or char[]
    if(is_char_type(eff_type.subtype()) ||
        eff_type.subtype().id()==ID_empty)
      map_entry.first->second=pointer_type(string_struct);
    else
    {
      const typet &subt=build_abstraction_type_rec(eff_type.subtype(), known);
      if(!subt.is_nil())
      {
        if(eff_type.id()==ID_array)
          map_entry.first->second=
            array_typet(subt, to_array_type(eff_type).size());
        else
          map_entry.first->second=pointer_type(subt);
      }
    }
  }
  else if(eff_type.id()==ID_struct || eff_type.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=to_struct_union_type(eff_type);

    struct_union_typet::componentst new_comp;
    for(const auto &comp : struct_union_type.components())
    {
      if(comp.get_anonymous())
        continue;
      typet subt=build_abstraction_type_rec(comp.type(), known);
      if(subt.is_nil())
        // also precludes structs with pointers to the same datatype
        continue;

      new_comp.push_back(struct_union_typet::componentt());
      new_comp.back().set_name(comp.get_name());
      new_comp.back().set_pretty_name(comp.get_pretty_name());
      new_comp.back().type()=subt;
    }
    if(!new_comp.empty())
    {
      struct_union_typet t(eff_type.id());
      t.components().swap(new_comp);
      map_entry.first->second=t;
    }
  }

  return map_entry.first->second;
}

bool string_abstractiont::build(const exprt &object, exprt &dest, bool write)
{
  const typet &abstract_type=build_abstraction_type(object.type());
  if(abstract_type.is_nil())
    return true;

  if(object.id()==ID_typecast)
  {
    if(build(to_typecast_expr(object).op(), dest, write))
      return true;

    return !(type_eq(dest.type(), abstract_type, ns) ||
        (dest.type().id()==ID_array &&
         abstract_type.id()==ID_pointer &&
         type_eq(dest.type().subtype(), abstract_type.subtype(), ns)));
  }

  if(object.id()==ID_string_constant)
  {
    const std::string &str_value =
      id2string(to_string_constant(object).get_value());
    // make sure we handle the case of a string constant with string-terminating
    // \0 in it
    const std::size_t str_len =
      std::min(str_value.size(), str_value.find('\0'));
    return build_symbol_constant(str_len, str_len+1, dest);
  }

  if(object.id()==ID_array && is_char_type(object.type().subtype()))
    return build_array(to_array_expr(object), dest, write);

  // other constants aren't useful
  if(object.is_constant())
    return true;

  if(object.id()==ID_symbol)
    return build_symbol(to_symbol_expr(object), dest);

  if(object.id()==ID_if)
    return build_if(to_if_expr(object), dest, write);

  if(object.id()==ID_member)
  {
    const member_exprt &o_mem=to_member_expr(object);
    dest=member_exprt(exprt(), o_mem.get_component_name(), abstract_type);
    return build_wrap(o_mem.struct_op(), dest.op0(), write);
  }

  if(object.id()==ID_dereference)
  {
    const dereference_exprt &o_deref=to_dereference_expr(object);
    dest=dereference_exprt(exprt(), abstract_type);
    return build_wrap(o_deref.pointer(), dest.op0(), write);
  }

  if(object.id()==ID_index)
  {
    const index_exprt &o_index=to_index_expr(object);
    dest=index_exprt(exprt(), o_index.index(), abstract_type);
    return build_wrap(o_index.array(), dest.op0(), write);
  }

  // handle pointer stuff
  if(object.type().id()==ID_pointer)
    return build_pointer(object, dest, write);

  return true;
}

bool string_abstractiont::build_if(const if_exprt &o_if,
    exprt &dest, bool write)
{
  if_exprt new_if(o_if.cond(), exprt(), exprt());

  // recursive calls
  bool op1_err=build_wrap(o_if.true_case(), new_if.true_case(), write);
  bool op2_err=build_wrap(o_if.false_case(), new_if.false_case(), write);
  if(op1_err && op2_err)
    return true;
  // at least one of them gave proper results
  if(op1_err)
  {
    new_if.type()=new_if.false_case().type();
    new_if.true_case()=build_unknown(new_if.type(), write);
  }
  else if(op2_err)
  {
    new_if.type()=new_if.true_case().type();
    new_if.false_case()=build_unknown(new_if.type(), write);
  }
  else
    new_if.type()=new_if.true_case().type();

  dest.swap(new_if);
  return false;
}

bool string_abstractiont::build_array(const array_exprt &object,
    exprt &dest, bool write)
{
  PRECONDITION(is_char_type(object.type().subtype()));

  // writing is invalid
  if(write)
    return true;

  const exprt &a_size=to_array_type(object.type()).size();
  mp_integer size;
  // don't do anything, if we cannot determine the size
  if(to_integer(a_size, size))
    return true;
  INVARIANT(
    size == object.operands().size(), "wrong number of array object arguments");

  exprt::operandst::const_iterator it=object.operands().begin();
  for(mp_integer i=0; i<size; ++i, ++it)
    if(it->is_zero())
      return build_symbol_constant(i, size, dest);

  return true;
}

bool string_abstractiont::build_pointer(const exprt &object,
    exprt &dest, bool write)
{
  PRECONDITION(object.type().id() == ID_pointer);

  pointer_arithmetict ptr(object);
  if(ptr.pointer.id()==ID_address_of)
  {
    const address_of_exprt &a=to_address_of_expr(ptr.pointer);

    if(a.object().id()==ID_index)
      return build_wrap(to_index_expr(a.object()).array(), dest, write);

    // writing is invalid
    if(write)
      return true;

    if(build_wrap(a.object(), dest, write))
      return true;
    dest=address_of_exprt(dest);
    return false;
  }
  else if(ptr.pointer.id()==ID_symbol &&
      is_char_type(object.type().subtype()))
    // recursive call; offset will be handled by pointer_offset in SIZE/LENGTH
    // checks
    return build_wrap(ptr.pointer, dest, write);

  // we don't handle other pointer arithmetic
  return true;
}

exprt string_abstractiont::build_unknown(whatt what, bool write)
{
  typet type=build_type(what);

  if(write)
    return exprt(ID_null_object, type);

  exprt result;

  switch(what)
  {
  case whatt::IS_ZERO:
    result=false_exprt();
    break;

  case whatt::LENGTH:
  case whatt::SIZE:
    result = side_effect_expr_nondett(type, source_locationt());
    break;
  }

  return result;
}

exprt string_abstractiont::build_unknown(const typet &type, bool write)
{
  if(write)
    return exprt(ID_null_object, type);

  // create an uninitialized dummy symbol
  // because of a lack of contextual information we can't build a nice name
  // here, but moving that into locals should suffice for proper operation
  irep_idt identifier=
    "$tmp::nondet_str#str$"+std::to_string(++temporary_counter);
  // ensure decl and initialization
  locals[identifier]=identifier;

  auxiliary_symbolt new_symbol;
  new_symbol.type=type;
  new_symbol.value.make_nil();
  new_symbol.name=identifier;
  new_symbol.module="$tmp";
  new_symbol.base_name=identifier;
  new_symbol.mode=ID_C;
  new_symbol.pretty_name=identifier;

  symbol_table.insert(std::move(new_symbol));

  return ns.lookup(identifier).symbol_expr();
}

bool string_abstractiont::build_symbol(const symbol_exprt &sym, exprt &dest)
{
  const symbolt &symbol=ns.lookup(sym.get_identifier());

  const typet &abstract_type=build_abstraction_type(symbol.type);
  CHECK_RETURN(!abstract_type.is_nil());

  irep_idt identifier="";

  if(current_args.find(symbol.name)!=current_args.end())
    identifier=id2string(symbol.name)+arg_suffix;
  else
  {
    identifier=id2string(symbol.name)+sym_suffix;
    if(symbol_table.symbols.find(identifier)==symbol_table.symbols.end())
      build_new_symbol(symbol, identifier, abstract_type);
  }

  const symbolt &str_symbol=ns.lookup(identifier);
  dest=str_symbol.symbol_expr();
  if(current_args.find(symbol.name)!=current_args.end() &&
      !is_ptr_argument(abstract_type))
    dest=dereference_exprt(dest, dest.type().subtype());

  return false;
}

void string_abstractiont::build_new_symbol(const symbolt &symbol,
    const irep_idt &identifier, const typet &type)
{
  if(!symbol.is_static_lifetime)
    locals[symbol.name]=identifier;

  auxiliary_symbolt new_symbol;
  new_symbol.type=type;
  new_symbol.value.make_nil();
  new_symbol.location=symbol.location;
  new_symbol.name=identifier;
  new_symbol.module=symbol.module;
  new_symbol.base_name=id2string(symbol.base_name)+sym_suffix;
  new_symbol.mode=symbol.mode;
  new_symbol.pretty_name=
    id2string(symbol.pretty_name.empty()?symbol.base_name:symbol.pretty_name)+
    sym_suffix;
  new_symbol.is_static_lifetime=symbol.is_static_lifetime;
  new_symbol.is_thread_local=symbol.is_thread_local;

  symbol_table.insert(std::move(new_symbol));

  if(symbol.is_static_lifetime)
  {
    goto_programt::targett dummy_loc=initialization.add_instruction();
    dummy_loc->source_location=symbol.location;
    make_decl_and_def(initialization, dummy_loc, identifier, symbol.name);
    initialization.instructions.erase(dummy_loc);
  }
}

bool string_abstractiont::build_symbol_constant(
  const mp_integer &zero_length,
  const mp_integer &buf_size,
  exprt &dest)
{
  irep_idt base="$string_constant_str_"+integer2string(zero_length)
    +"_"+integer2string(buf_size);
  irep_idt identifier="string_abstraction::"+id2string(base);

  if(symbol_table.symbols.find(identifier)==
     symbol_table.symbols.end())
  {
    auxiliary_symbolt new_symbol;
    new_symbol.type=string_struct;
    new_symbol.value.make_nil();
    new_symbol.name=identifier;
    new_symbol.base_name=base;
    new_symbol.mode=ID_C;
    new_symbol.pretty_name=base;
    new_symbol.is_static_lifetime=true;
    new_symbol.is_thread_local=false;
    new_symbol.is_file_local=false;

    {
      struct_exprt value(string_struct);
      value.operands().resize(3);

      value.op0()=true_exprt();
      value.op1()=from_integer(zero_length, build_type(whatt::LENGTH));
      value.op2()=from_integer(buf_size, build_type(whatt::SIZE));

      // initialization
      goto_programt::targett assignment1=initialization.add_instruction();
      assignment1->make_assignment();
      assignment1->code=code_assignt(new_symbol.symbol_expr(), value);
    }

    symbol_table.insert(std::move(new_symbol));
  }

  dest=address_of_exprt(symbol_exprt(identifier, string_struct));

  return false;
}

void string_abstractiont::move_lhs_arithmetic(exprt &lhs, exprt &rhs)
{
  if(lhs.id()==ID_minus)
  {
    // move op1 to rhs
    exprt rest=lhs.op0();
    rhs=plus_exprt(rhs, lhs.op1());
    rhs.type()=lhs.type();
    lhs=rest;
  }
}

goto_programt::targett string_abstractiont::abstract_pointer_assign(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_assignt &assign=to_code_assign(target->code);

  exprt &lhs=assign.lhs();
  exprt rhs=assign.rhs();
  exprt *rhsp=&(assign.rhs());

  while(rhsp->id()==ID_typecast)
    rhsp=&(rhsp->op0());

  const typet &abstract_type=build_abstraction_type(lhs.type());
  if(abstract_type.is_nil())
    return target;

  exprt new_lhs, new_rhs;
  if(build_wrap(lhs, new_lhs, true))
    return target;

  bool unknown=(abstract_type!=build_abstraction_type(rhsp->type()) ||
      build_wrap(rhs, new_rhs, false));
  if(unknown)
    new_rhs=build_unknown(abstract_type, false);

  if(lhs.type().id()==ID_pointer && !unknown)
  {
    goto_programt::instructiont assignment;
    assignment.make_assignment();
    assignment.source_location=target->source_location;
    assignment.function=target->function;
    assignment.code=code_assignt(new_lhs, new_rhs);
    assignment.code.add_source_location()=target->source_location;
    dest.insert_before_swap(target, assignment);
    ++target;

    return target;
  }
  else
  {
    return value_assignments(dest, target, new_lhs, new_rhs);
  }
}

goto_programt::targett string_abstractiont::abstract_char_assign(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_assignt &assign=to_code_assign(target->code);

  exprt &lhs=assign.lhs();
  exprt *rhsp=&(assign.rhs());

  while(rhsp->id()==ID_typecast)
    rhsp=&(rhsp->op0());

  // we only care if the constant zero is assigned
  if(!rhsp->is_zero())
    return target;

  // index into a character array
  if(lhs.id()==ID_index)
  {
    const index_exprt &i_lhs=to_index_expr(lhs);

    exprt new_lhs;
    if(!build_wrap(i_lhs.array(), new_lhs, true))
    {
      exprt i2=member(new_lhs, whatt::LENGTH);
      INVARIANT(
        i2.is_not_nil(),
        "failed to create length-component for the left-hand-side");

      exprt new_length=i_lhs.index();
      make_type(new_length, i2.type());

      if_exprt min_expr(binary_relation_exprt(new_length, ID_lt, i2),
          new_length, i2);

      return char_assign(dest, target, new_lhs, i2, min_expr);
    }
  }
  else if(lhs.id()==ID_dereference)
  {
    pointer_arithmetict ptr(to_dereference_expr(lhs).pointer());
    exprt new_lhs;
    if(!build_wrap(ptr.pointer, new_lhs, true))
    {
      const exprt i2=member(new_lhs, whatt::LENGTH);
      INVARIANT(
        i2.is_not_nil(),
        "failed to create length-component for the left-hand-side");

      make_type(ptr.offset, build_type(whatt::LENGTH));
      return
        char_assign(
          dest,
          target,
          new_lhs,
          i2,
          ptr.offset.is_nil()?
            from_integer(0, build_type(whatt::LENGTH)):
            ptr.offset);
    }
  }

  return target;
}

goto_programt::targett string_abstractiont::char_assign(
  goto_programt &dest,
  goto_programt::targett target,
  const exprt &new_lhs,
  const exprt &lhs,
  const exprt &rhs)
{
  goto_programt tmp;

  const exprt i1=member(new_lhs, whatt::IS_ZERO);
  INVARIANT(
    i1.is_not_nil(),
    "failed to create is_zero-component for the left-hand-side");

  goto_programt::targett assignment1=tmp.add_instruction();
  assignment1->make_assignment();
  assignment1->source_location=target->source_location;
  assignment1->function=target->function;
  assignment1->code=code_assignt(i1, true_exprt());
  assignment1->code.add_source_location()=target->source_location;

  goto_programt::targett assignment2=tmp.add_instruction();
  assignment2->make_assignment();
  assignment2->source_location=target->source_location;
  assignment2->function=target->function;
  assignment2->code=code_assignt(lhs, rhs);
  assignment2->code.add_source_location()=target->source_location;

  move_lhs_arithmetic(
      assignment2->code.op0(),
      assignment2->code.op1());

  dest.insert_before_swap(target, tmp);
  ++target;
  ++target;

  return target;
}

goto_programt::targett string_abstractiont::value_assignments(
  goto_programt &dest,
  goto_programt::targett target,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.id()==ID_if)
    return value_assignments_if(dest, target, lhs, to_if_expr(rhs));

  PRECONDITION(type_eq(lhs.type(), rhs.type(), ns));

  if(lhs.type().id()==ID_array)
  {
    const exprt &a_size=to_array_type(lhs.type()).size();
    mp_integer size;
    // don't do anything, if we cannot determine the size
    if(to_integer(a_size, size))
      return target;
    for(mp_integer i=0; i<size; ++i)
      target=value_assignments(dest, target,
          index_exprt(lhs, from_integer(i, a_size.type())),
          index_exprt(rhs, from_integer(i, a_size.type())));
  }
  else if(lhs.type().id()==ID_pointer)
    return value_assignments(dest, target,
        dereference_exprt(lhs, lhs.type().subtype()),
        dereference_exprt(rhs, rhs.type().subtype()));
  else if(lhs.type()==string_struct)
    return value_assignments_string_struct(dest, target, lhs, rhs);
  else if(lhs.type().id()==ID_struct || lhs.type().id()==ID_union)
  {
    const struct_union_typet &struct_union_type=
      to_struct_union_type(lhs.type());

    for(const auto &comp : struct_union_type.components())
    {
      INVARIANT(
        !comp.get_name().empty(), "struct/union components must have a name");

      target=value_assignments(dest, target,
          member_exprt(lhs, comp.get_name(), comp.type()),
          member_exprt(rhs, comp.get_name(), comp.type()));
    }
  }

  return target;
}

goto_programt::targett string_abstractiont::value_assignments_if(
  goto_programt &dest,
  goto_programt::targett target,
  const exprt &lhs, const if_exprt &rhs)
{
  goto_programt tmp;

  goto_programt::targett goto_else=tmp.add_instruction(GOTO);
  goto_programt::targett goto_out=tmp.add_instruction(GOTO);
  goto_programt::targett else_target=tmp.add_instruction(SKIP);
  goto_programt::targett out_target=tmp.add_instruction(SKIP);

  goto_else->function=target->function;
  goto_else->source_location=target->source_location;
  goto_else->make_goto(else_target, boolean_negate(rhs.cond()));

  goto_out->function=target->function;
  goto_out->source_location=target->source_location;
  goto_out->make_goto(out_target, true_exprt());

  else_target->function=target->function;
  else_target->source_location=target->source_location;

  out_target->function=target->function;
  out_target->source_location=target->source_location;

  value_assignments(tmp, goto_out, lhs, rhs.true_case());
  value_assignments(tmp, else_target, lhs, rhs.false_case());

  goto_programt::targett last=target;
  ++last;
  dest.insert_before_swap(target, tmp);
  --last;

  return last;
}

goto_programt::targett string_abstractiont::value_assignments_string_struct(
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs, const exprt &rhs)
{
  // copy all the values
  goto_programt tmp;

  {
    goto_programt::targett assignment=tmp.add_instruction(ASSIGN);
    assignment->code=code_assignt(
        member(lhs, whatt::IS_ZERO),
        member(rhs, whatt::IS_ZERO));
    assignment->code.add_source_location()=target->source_location;
    assignment->function=target->function;
    assignment->source_location=target->source_location;
  }

  {
    goto_programt::targett assignment=tmp.add_instruction(ASSIGN);
    assignment->code=code_assignt(
        member(lhs, whatt::LENGTH),
        member(rhs, whatt::LENGTH));
    assignment->code.add_source_location()=target->source_location;
    assignment->function=target->function;
    assignment->source_location=target->source_location;
  }

  {
    goto_programt::targett assignment=tmp.add_instruction(ASSIGN);
    assignment->code=code_assignt(
        member(lhs, whatt::SIZE),
        member(rhs, whatt::SIZE));
    assignment->code.add_source_location()=target->source_location;
    assignment->function=target->function;
    assignment->source_location=target->source_location;
  }

  goto_programt::targett last=target;
  ++last;
  dest.insert_before_swap(target, tmp);
  --last;

  return last;
}

exprt string_abstractiont::member(const exprt &a, whatt what)
{
  if(a.is_nil())
    return a;

  PRECONDITION_WITH_DIAGNOSTICS(
    type_eq(a.type(), string_struct, ns) || is_ptr_string_struct(a.type()),
    "either the expression is not a string or it is not a pointer to one");

  exprt struct_op=
    a.type().id()==ID_pointer?
    dereference_exprt(a, string_struct):a;

  irep_idt component_name;

  switch(what)
  {
  case whatt::IS_ZERO: component_name="is_zero"; break;
  case whatt::SIZE: component_name="size"; break;
  case whatt::LENGTH: component_name="length"; break;
  }

  return member_exprt(struct_op, component_name, build_type(what));
}
