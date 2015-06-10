/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/replace_expr.h>
#include <util/expr_util.h>
#include <util/rational_tools.h>
#include <util/source_location.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/pointer_predicates.h>
#include <util/pointer_offset_size.h>
#include <util/vtable.h>

#include <linking/zero_initializer.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::do_prob_uniform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_prob_uniform(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &identifier=function.get(ID_identifier);

  // make it a side effect if there is an LHS
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have two arguments";
  }

  if(lhs.is_nil())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have LHS";
  }

  exprt rhs=side_effect_exprt("prob_uniform", lhs.type());
  rhs.add_source_location()=function.source_location();

  if(lhs.type().id()!=ID_unsignedbv &&
     lhs.type().id()!=ID_signedbv)
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected other type";
  }

  if(arguments[0].type().id()!=lhs.type().id() ||
     arguments[1].type().id()!=lhs.type().id())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected operands to be of same type as LHS";
  }

  if(!arguments[0].is_constant() ||
     !arguments[1].is_constant())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected operands to be constant literals";
  }

  mp_integer lb, ub;

  if(to_integer(arguments[0], lb) ||
     to_integer(arguments[1], ub))
  {
    err_location(function);
    throw "error converting operands";
  }

  if(lb > ub)
  {
    err_location(function);
    throw "expected lower bound to be smaller or equal to the upper bound";
  }

  rhs.copy_to_operands(arguments[0], arguments[1]);

  code_assignt assignment(lhs, rhs);
  assignment.add_source_location()=function.source_location();
  copy(assignment, ASSIGN, dest);
}

/*******************************************************************\

Function: goto_convertt::do_prob_coin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_prob_coin(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &identifier=function.get(ID_identifier);

  // make it a side effect if there is an LHS
  if(arguments.size()!=2) 
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have two arguments";
  }
  
  if(lhs.is_nil())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have LHS";
  }

  exprt rhs=side_effect_exprt("prob_coin", lhs.type());
  rhs.add_source_location()=function.source_location();

  if(lhs.type()!=bool_typet())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected bool";
  }

  if(arguments[0].type().id()!=ID_unsignedbv ||
     arguments[0].id()!=ID_constant)
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected first "
          "operand to be a constant literal of type unsigned long";
  }

  mp_integer num, den;

  if(to_integer(arguments[0], num) ||
     to_integer(arguments[1], den))
  {
    err_location(function);
    throw "error converting operands";
  }

  if(num-den > mp_integer(0))
  {
    err_location(function);
    throw "probability has to be smaller than 1";
  }

  if(den == mp_integer(0))
  {
    err_location(function);
    throw "denominator may not be zero";
  }

  rationalt numerator(num), denominator(den);
  rationalt prob = numerator / denominator;

  rhs.copy_to_operands(from_rational(prob));

  code_assignt assignment(lhs, rhs);
  assignment.add_source_location()=function.source_location();
  copy(assignment, ASSIGN, dest);
}

/*******************************************************************\

Function: goto_convertt::do_printf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_printf(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &f_id=function.get(ID_identifier);

  if(f_id==CPROVER_PREFIX "printf" ||
     f_id=="printf")
  {
    typet return_type=static_cast<const typet &>(function.type().find(ID_return_type));
    side_effect_exprt printf_code(ID_printf, return_type);

    printf_code.operands()=arguments;
    printf_code.add_source_location()=function.source_location();

    if(lhs.is_not_nil())
    {
      code_assignt assignment(lhs, printf_code);
      assignment.add_source_location()=function.source_location();
      copy(assignment, ASSIGN, dest);
    }
    else
    {
      printf_code.id(ID_code);
      printf_code.type()=typet(ID_code);
      copy(to_code(printf_code), OTHER, dest);
    }
  }
  else
    assert(false);
}

/*******************************************************************\

Function: goto_convertt::do_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_input(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet input_code;
  input_code.set_statement(ID_input);
  input_code.operands()=arguments;
  input_code.add_source_location()=function.source_location();
  
  if(arguments.size()<2)
  {
    err_location(function);
    throw "input takes at least two arguments";
  }
    
  copy(input_code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_cover(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet output_code;
  output_code.set_statement(ID_output);
  output_code.add_source_location()=function.source_location();

  if(arguments.size()!=1)
  {
    err_location(function);
    throw "cover takes one argument";
  }
  
  // build string constant
  exprt string_constant(ID_string_constant);
  string_constant.type()=array_typet();
  string_constant.type().subtype()=char_type();
  string_constant.set(ID_value, ID_cover);
  
  index_exprt index_expr;
  index_expr.type()=char_type();
  index_expr.array()=string_constant;
  index_expr.index()=gen_zero(index_type());
  
  output_code.copy_to_operands(address_of_exprt(index_expr));
  
  forall_expr(it, arguments)
    output_code.copy_to_operands(*it);
    
  copy(output_code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_output(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet output_code;
  output_code.set_statement(ID_output);
  output_code.operands()=arguments;
  output_code.add_source_location()=function.source_location();
  
  if(arguments.size()<2)
  {
    err_location(function);
    throw "output takes at least two arguments";
  }
    
  copy(output_code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_atomic_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_atomic_begin(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(lhs.is_not_nil())
  {
    err_location(lhs);
    throw "atomic_begin does not expect an LHS";
  }

  if(!arguments.empty())
  {
    err_location(function);
    throw "atomic_begin takes no arguments";
  }

  goto_programt::targett t=dest.add_instruction(ATOMIC_BEGIN);
  t->source_location=function.source_location();
}

/*******************************************************************\

Function: goto_convertt::do_atomic_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_atomic_end(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(lhs.is_not_nil())
  {
    err_location(lhs);
    throw "atomic_end does not expect an LHS";
  }

  if(!arguments.empty())
  {
    err_location(function);
    throw "atomic_end takes no arguments";
  }

  goto_programt::targett t=dest.add_instruction(ATOMIC_END);
  t->source_location=function.source_location();
}

/*******************************************************************\

Function: goto_convertt::do_cpp_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_cpp_new(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  if(lhs.is_nil())
    throw "do_cpp_new without lhs is yet to be implemented";
  
  // build size expression
  exprt object_size=
    static_cast<const exprt &>(rhs.find(ID_sizeof));

  bool new_array=rhs.get(ID_statement)==ID_cpp_new_array;
  
  exprt count;

  if(new_array)
  {
    count=static_cast<const exprt &>(rhs.find(ID_size));

    if(count.type()!=object_size.type())
      count.make_typecast(object_size.type());

    // might have side-effect
    clean_expr(count, dest);
  }

  exprt tmp_symbol_expr;

  // is this a placement new?
  if(rhs.operands().empty()) // no, "regular" one
  {
    // call __new or __new_array
    exprt new_symbol=
      ns.lookup(new_array?"__new_array":"__new").symbol_expr();
    
    const code_typet &code_type=
      to_code_type(new_symbol.type());

    const typet &return_type=
      code_type.return_type();

    assert(code_type.parameters().size()==1 ||
           code_type.parameters().size()==2);

    const symbolt &tmp_symbol=
      new_tmp_symbol(return_type, "new", dest, rhs.source_location());
    
    tmp_symbol_expr=tmp_symbol.symbol_expr();
    
    code_function_callt new_call;
    new_call.function()=new_symbol;
    if(new_array) new_call.arguments().push_back(count);
    new_call.arguments().push_back(object_size);
    new_call.set("#type", lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.add_source_location()=rhs.source_location();
    
    convert(new_call, dest);
  }
  else if(rhs.operands().size()==1)
  {
    // call __placement_new
    exprt new_symbol=
      ns.lookup(new_array?"__placement_new_array":"__placement_new").symbol_expr();
    
    const code_typet &code_type=
      to_code_type(new_symbol.type());

    const typet &return_type=code_type.return_type();
    
    assert(code_type.parameters().size()==2 ||
           code_type.parameters().size()==3);

    const symbolt &tmp_symbol=
      new_tmp_symbol(return_type, "new", dest, rhs.source_location());

    tmp_symbol_expr=tmp_symbol.symbol_expr();

    code_function_callt new_call;
    new_call.function()=new_symbol;
    if(new_array) new_call.arguments().push_back(count);
    new_call.arguments().push_back(object_size);
    new_call.arguments().push_back(rhs.op0()); // memory location
    new_call.set("#type", lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.add_source_location()=rhs.source_location();

    for(unsigned i=0; i<code_type.parameters().size(); i++)
      if(new_call.arguments()[i].type()!=code_type.parameters()[i].type())
        new_call.arguments()[i].make_typecast(code_type.parameters()[i].type());
    
    convert(new_call, dest);
  }
  else
    throw "cpp_new expected to have 0 or 1 operands";

  goto_programt::targett t_n=dest.add_instruction(ASSIGN);
  t_n->code=code_assignt(
    lhs, typecast_exprt(tmp_symbol_expr, lhs.type()));
  t_n->source_location=rhs.find_location();
    
  // grab initializer
  goto_programt tmp_initializer;
  cpp_new_initializer(lhs, rhs, tmp_initializer);

  dest.destructive_append(tmp_initializer);
}

namespace {
symbol_exprt get_vt(const irep_idt &class_name) {
  const std::string &name(id2string(class_name));
  const irep_idt vttype_name(vtnamest::get_type(name));
  const irep_idt vt_name(vtnamest::get_table(name));
  const symbol_typet vttype(vttype_name);
  return symbol_exprt(vt_name, vttype);
}

const dereference_exprt cast_if_necessary(const exprt &lhs,
    const irep_idt &ptr_class, const irep_idt &vt_class) {
  const symbol_typet class_type(vt_class);
  if (ptr_class == vt_class) return dereference_exprt(lhs, class_type);
  const symbol_typet target_type(ptr_class);
  const typecast_exprt cast(lhs, pointer_typet(target_type));
  return dereference_exprt(cast, target_type);
}

void assign_vtpointer(goto_programt &dest, const namespacet &ns,
    const exprt &lhs, const irep_idt &ptr_class, const irep_idt &vt_class,
    const source_locationt &location) {
  const symbol_exprt ptr_vt(get_vt(ptr_class));
  const symbol_exprt vt(get_vt(vt_class));
  const dereference_exprt lhs_ref(cast_if_necessary(lhs, ptr_class, vt_class));
  const std::string memb_name(vtnamest::get_pointer(id2string(ptr_class)));
  const pointer_typet ptr_vt_type(ptr_vt.type());
  const member_exprt vtmember(lhs_ref, memb_name, ptr_vt_type);
  const address_of_exprt vtable_ptr(vt);
  const goto_programt::targett instr(dest.add_instruction(ASSIGN));
  instr->source_location = location;
  if (ptr_class == vt_class) {
    instr->code = code_assignt(vtmember, vtable_ptr);
  } else {
    const typecast_exprt cast(vtable_ptr, ptr_vt_type);
    instr->code = code_assignt(vtmember, cast);
  }
}

bool is_type_missing(const namespacet &ns, const symbol_typet &type)
{
  return !ns.get_symbol_table().has_symbol(type.get_identifier());
}

void assign_vtpointers(goto_programt &dest, const namespacet &ns,
    const exprt &lhs, const symbol_typet &class_type,
    const source_locationt &location)
{
  if (is_type_missing(ns, class_type)) return;
  const irep_idt &class_name(class_type.get_identifier());
  const irep_idt vtname(vtnamest::get_table(id2string(class_name)));
  if (ns.get_symbol_table().has_symbol(vtname)) {
    const class_typet &full_class_type(to_class_type(ns.follow(class_type)));
    const irept::subt &bases(full_class_type.bases());
    for (irept::subt::const_iterator it=bases.begin(); it != bases.end(); ++it) {
      const typet &type(static_cast<const typet &>(it->find(ID_type)));
      const symbol_typet &parent_type(to_symbol_type(type));
      if (is_type_missing(ns, parent_type)) continue;
      const irep_idt &parent_name(parent_type.get_identifier());
      const irep_idt parent_vtname(vtnamest::get_table(id2string(parent_name)));
      if(!ns.get_symbol_table().has_symbol(parent_vtname)) continue;
      assign_vtpointer(dest, ns, lhs, parent_name, class_name, location);
    }
    assign_vtpointer(dest, ns, lhs, class_name, class_name, location);
  }
}
}

/*******************************************************************\

Function: goto_convertt::do_java_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_java_new(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  if(lhs.is_nil())
    throw "do_java_new without lhs is yet to be implemented";
    
  source_locationt location=rhs.source_location();

  assert(rhs.operands().empty());

  typet object_type=rhs.type().subtype();
  
  // build size expression
  exprt object_size=size_of_expr(object_type, ns);
  
  if(object_size.is_nil())
    throw "do_java_new got nil object_size";

  // we produce a malloc side-effect, which stays
  side_effect_exprt malloc_expr(ID_malloc);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.type()=pointer_typet(object_type);

  goto_programt::targett t_n=dest.add_instruction(ASSIGN);
  t_n->code=code_assignt(lhs, malloc_expr);
  t_n->source_location=location;
  
  // zero-initialize the object
  dereference_exprt deref(lhs, object_type);
  exprt zero_object=zero_initializer(object_type, location, ns, get_message_handler());
  goto_programt::targett t_i=dest.add_instruction(ASSIGN);
  t_i->code=code_assignt(deref, zero_object);
  t_i->source_location=location;

  assign_vtpointers(dest, ns, lhs, to_symbol_type(object_type), location);
}

/*******************************************************************\

Function: goto_convertt::do_java_new_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_java_new_array(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  if(lhs.is_nil())
    throw "do_java_new without lhs is yet to be implemented";
    
  source_locationt location=rhs.source_location();

  assert(rhs.operands().size()>=1); // one per dimension

  typet object_type=rhs.type().subtype();
  
  // build size expression
  exprt object_size=size_of_expr(object_type, ns);
  
  if(object_size.is_nil())
    throw "do_java_new got nil object_size";

  // we produce a malloc side-effect, which stays
  side_effect_exprt malloc_expr(ID_malloc);
  malloc_expr.copy_to_operands(object_size);
  malloc_expr.type()=pointer_typet(object_type);

  goto_programt::targett t_n=dest.add_instruction(ASSIGN);
  t_n->code=code_assignt(lhs, malloc_expr);
  t_n->source_location=location;
  
  // multi-dimensional?
  
  assert(object_type.id()==ID_struct);
  const struct_typet &struct_type=to_struct_type(object_type);
  assert(struct_type.components().size()==2);

  // if it's an array, we need to set the length field
  dereference_exprt deref(lhs, object_type);
  member_exprt length(deref, struct_type.components()[0].get_name(), struct_type.components()[0].type());
  goto_programt::targett t_s=dest.add_instruction(ASSIGN);
  t_s->code=code_assignt(length, rhs.op0());
  t_s->source_location=location;
  
  // we also need to allocate space for the data
  member_exprt data(deref, struct_type.components()[1].get_name(), struct_type.components()[1].type());
  side_effect_exprt data_cpp_new_expr(ID_cpp_new_array, data.type());
  data_cpp_new_expr.set(ID_size, rhs.op0());
  goto_programt::targett t_p=dest.add_instruction(ASSIGN);
  t_p->code=code_assignt(data, data_cpp_new_expr);
  t_p->source_location=location;
  
  // zero-initialize the data
  exprt zero_element=gen_zero(data.type().subtype());
  codet array_set(ID_array_set);
  array_set.copy_to_operands(data, zero_element);
  goto_programt::targett t_d=dest.add_instruction(OTHER);
  t_d->code=array_set;
  t_d->source_location=location;

  if(rhs.operands().size()>=2)
  {
    // produce
    // for(int i=0; i<size; i++) tmp[i]=java_new(dim-1);
    // This will be converted recursively.
    
    goto_programt tmp;

    symbol_exprt tmp_i=
      new_tmp_symbol(index_type(), "index", tmp, location).symbol_expr();

    code_fort for_loop;
    
    side_effect_exprt sub_java_new=rhs;
    sub_java_new.operands().erase(sub_java_new.operands().begin());
    sub_java_new.type()=data.type().subtype();
    
    side_effect_exprt inc(ID_assign);
    inc.operands().resize(2);
    inc.op0()=tmp_i;
    inc.op1()=plus_exprt(tmp_i, gen_one(tmp_i.type()));
    
    dereference_exprt deref_expr(plus_exprt(data, tmp_i), data.type().subtype());
    
    for_loop.init()=code_assignt(tmp_i, gen_zero(tmp_i.type()));
    for_loop.cond()=binary_relation_exprt(tmp_i, ID_lt, rhs.op0());
    for_loop.iter()=inc;
    for_loop.body()=code_skipt();
    for_loop.body()=code_assignt(deref_expr, sub_java_new);

    convert(for_loop, tmp);
    dest.destructive_append(tmp);
  }
}

/*******************************************************************\

Function: goto_convertt::cpp_new_initializer

  Inputs:

 Outputs:

 Purpose: builds a goto program for object initialization
          after new

\*******************************************************************/

void goto_convertt::cpp_new_initializer(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  exprt initializer=
    static_cast<const exprt &>(rhs.find(ID_initializer));

  if(initializer.is_not_nil())
  {
    if(rhs.get_statement()=="cpp_new[]")
    {
      // build loop
    }
    else if(rhs.get_statement()==ID_cpp_new)
    {
      // just one object
      exprt deref_lhs(ID_dereference, rhs.type().subtype());
      deref_lhs.copy_to_operands(lhs);
      
      replace_new_object(deref_lhs, initializer);
      convert(to_code(initializer), dest);
    }
    else
      assert(false);
  }
}

/*******************************************************************\

Function: goto_convertt::get_array_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt goto_convertt::get_array_argument(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    assert(src.operands().size()==1);
    return get_array_argument(src.op0());
  }

  if(src.id()!=ID_address_of)
  {
    err_location(src);
    throw "expected array-pointer as argument";
  }
  
  assert(src.operands().size()==1);

  if(src.op0().id()!=ID_index)
  {
    err_location(src);
    throw "expected array-element as argument";
  }
  
  assert(src.op0().operands().size()==2);

  if(ns.follow(src.op0().op0().type()).id()!=ID_array)
  {
    err_location(src);
    throw "expected array as argument";
  }

  return src.op0().op0();
}

/*******************************************************************\

Function: goto_convertt::do_array_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_array_set(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "array_set expects two arguments";
  }

  codet array_set_statement;
  array_set_statement.set_statement(ID_array_set);
  array_set_statement.operands()=arguments;

  copy(array_set_statement, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_array_copy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_array_copy(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "array_copy expects two arguments";
  }

  codet array_set_statement;
  array_set_statement.set_statement(ID_array_copy);
  array_set_statement.operands()=arguments;

  copy(array_set_statement, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_array_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_array_equal(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "array_equal expects two arguments";
  }
  
  const typet &arg0_type=ns.follow(arguments[0].type());
  const typet &arg1_type=ns.follow(arguments[1].type());
  
  if(arg0_type.id()!=ID_pointer ||
     arg1_type.id()!=ID_pointer)
  {
    err_location(function);
    throw "array_equal expects pointer arguments";
  }
  
  if(lhs.is_not_nil())
  {
    code_assignt assignment;
    
    // add dereferencing here
    dereference_exprt lhs_array, rhs_array;
    lhs_array.op0()=arguments[0];
    rhs_array.op0()=arguments[1];
    lhs_array.type()=arg0_type.subtype();
    rhs_array.type()=arg1_type.subtype();
    
    assignment.lhs()=lhs;
    assignment.rhs()=binary_exprt(
      lhs_array, ID_array_equal, rhs_array, lhs.type());
    
    convert(assignment, dest);
  }
}

/*******************************************************************\

Function: is_lvalue

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_lvalue(const exprt &expr)
{
  if(expr.id()==ID_index)
    return is_lvalue(to_index_expr(expr).op0());
  else if(expr.id()==ID_member)
    return is_lvalue(to_member_expr(expr).op0());
  else if(expr.id()==ID_dereference)
    return true;
  else if(expr.id()==ID_symbol)
    return true;
  else
    return false;
}

/*******************************************************************\

Function: make_va_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt make_va_list(const exprt &expr)
{
  // we first strip any typecast
  if(expr.id()==ID_typecast)
    return make_va_list(to_typecast_expr(expr).op());

  // if it's an address of an lvalue, we take that
  if(expr.id()==ID_address_of &&
     expr.operands().size()==1 &&
     is_lvalue(expr.op0()))
    return expr.op0();

  return expr;
}

/*******************************************************************\

Function: goto_convertt::do_function_call_symbol

  Inputs:

 Outputs:

 Purpose: add function calls to function queue for later
          processing

\*******************************************************************/

void goto_convertt::do_function_call_symbol(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(function.get_bool("#invalid_object"))
    return; // ignore

  // lookup symbol
  const irep_idt &identifier=function.get(ID_identifier);

  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
  {
    err_location(function);
    throw "error: function `"+id2string(identifier)+"' not found";
  }

  if(symbol->type.id()!=ID_code)
  {
    err_location(function);
    throw "error: function `"+id2string(identifier)+"' type mismatch: expected code";
  }
  
  if(identifier==CPROVER_PREFIX "parameter_predicates" || 
     identifier==CPROVER_PREFIX "return_predicates")
  {
    if(arguments.size() != 0)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have no arguments";
    }

    goto_programt::targett t = dest.add_instruction(OTHER);
    t->source_location = function.source_location();
    t->source_location.set("user-provided", true);
    if(identifier==CPROVER_PREFIX "parameter_predicates")
    {
      t->code = codet(ID_user_specified_parameter_predicates);
      t->code.set_statement(ID_user_specified_parameter_predicates);
    }
    else
    {
      t->code = codet(ID_user_specified_return_predicates);
      t->code.set_statement(ID_user_specified_return_predicates);
    }
  }
  else if(identifier==CPROVER_PREFIX "predicate")
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    goto_programt::targett t=dest.add_instruction(OTHER);
    t->guard=arguments.front();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->code=codet(ID_user_specified_predicate);
  }
  else if(identifier==CPROVER_PREFIX "assume" ||
          identifier=="__VERIFIER_assume")
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    goto_programt::targett t=dest.add_instruction(ASSUME);
    t->guard=arguments.front();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    
    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(identifier=="__VERIFIER_error")
  {
    if(!arguments.empty())
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have no arguments";
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(has_prefix(id2string(identifier), "java::java.lang.AssertionError.<init>:"))
  {
    // insert function call anyway
    code_function_callt function_call;
    function_call.lhs()=lhs;
    function_call.function()=function;
    function_call.arguments()=arguments;
    function_call.add_source_location()=function.source_location();

    copy(function_call, FUNCTION_CALL, dest);

    if(arguments.size()!=1 && arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one or two arguments";
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);    
  }
  else if(identifier=="assert" &&
          !ns.lookup(identifier).location.get_function().empty())
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=arguments.front();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment("assertion "+id2string(from_expr(ns, "", t->guard)));
    
    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(identifier==CPROVER_PREFIX "assert")
  {
    if(arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have two arguments";
    }
    
    const irep_idt description=
      get_string_constant(arguments[1]);

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=arguments[0];
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    
    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(identifier==CPROVER_PREFIX "printf")
  {
    do_printf(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "input" ||
          identifier=="__CPROVER::input")
  {
    do_input(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "cover" ||
          identifier=="__CPROVER::cover")
  {
    do_cover(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "output" ||
          identifier=="__CPROVER::output")
  {
    do_output(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_begin" ||
          identifier=="__CPROVER::atomic_begin")
  {
    do_atomic_begin(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_end" ||
          identifier=="__CPROVER::atomic_end")
  {
    do_atomic_end(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "prob_biased_coin")
  {
    do_prob_coin(lhs, function, arguments, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "prob_uniform_"))
  {
    do_prob_uniform(lhs, function, arguments, dest);
  }
  else if(has_prefix(id2string(identifier), "nondet_") ||
          has_prefix(id2string(identifier), "__VERIFIER_nondet_"))
  {
    // make it a side effect if there is an LHS
    if(lhs.is_nil()) return;
    
    exprt rhs;
    
    // We need to special-case for _Bool, which
    // can only be 0 or 1.
    if(lhs.type().id()==ID_c_bool)
    {
      rhs=side_effect_expr_nondett(bool_typet());
      rhs.add_source_location()=function.source_location();
      rhs.set(ID_C_identifier, identifier);
      rhs=typecast_exprt(rhs, lhs.type());
    } 
    else
    {
      rhs=side_effect_expr_nondett(lhs.type());
      rhs.add_source_location()=function.source_location();
      rhs.set(ID_C_identifier, identifier);
    }

    code_assignt assignment(lhs, rhs);
    assignment.add_source_location()=function.source_location();
    copy(assignment, ASSIGN, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "uninterpreted_"))
  {
    // make it a side effect if there is an LHS
    if(lhs.is_nil()) return;

    function_application_exprt rhs;
    rhs.type()=lhs.type();
    rhs.add_source_location()=function.source_location();
    rhs.function()=function;
    rhs.arguments()=arguments;

    code_assignt assignment(lhs, rhs);
    assignment.add_source_location()=function.source_location();
    copy(assignment, ASSIGN, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "array_set"))
  {
    do_array_set(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_equal" ||
          identifier=="__CPROVER::array_equal")
  {
    do_array_equal(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_copy" ||
          identifier=="__CPROVER::array_equal")
  {
    do_array_copy(lhs, function, arguments, dest);
  }
  else if(identifier=="printf")
  /*
          identifier=="fprintf" ||
          identifier=="sprintf" ||
          identifier=="snprintf")
  */
  {
    do_printf(lhs, function, arguments, dest);
  }
  else if(identifier=="__assert_fail")
  {
    // __assert_fail is Linux
    // These take four arguments:
    // "expression", "file.c", line, __func__

    if(arguments.size()!=4)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have four arguments";
    }
    
    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="_assert")
  {
    // MingW has
    // void _assert (const char*, const char*, int);
    // with three arguments:
    // "expression", "file.c", line

    if(arguments.size()!=3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have three arguments";
    }
    
    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="__assert_c99")
  {
    // This has been seen in Solaris 11.
    // Signature:
    // void __assert_c99(const char *desc, const char *file, int line, const char *func);

    if(arguments.size()!=4)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have four arguments";
    }
    
    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="__assert_rtn" ||
          identifier=="__assert")
  {
    // __assert_rtn has been seen on MacOS;
    // __assert is FreeBSD and Solaris 11.
    // These take four arguments:
    // __func__, "file.c", line, "expression"
    // On Solaris 11, it's three arguments:
    // "expression", "file", line
    
    irep_idt description;
    
    if(arguments.size()==4)
    {
      description=
        "assertion "+id2string(get_string_constant(arguments[3]));
    }
    else if(arguments.size()==3)
    {
      description=
        "assertion "+id2string(get_string_constant(arguments[1]));
    }
    else
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have four arguments";
    }

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="__assert_func")
  {
    // __assert_func is newlib (used by, e.g., cygwin)
    // These take four arguments:
    // "file.c", line, __func__, "expression"
    if(arguments.size()!=4)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have four arguments";
    }

    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[3]));
      goto_programt::targett t=dest.add_instruction(ASSERT);

    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="_wassert")
  {
    // This is Windows. The arguments are
    // L"expression", L"file.c", line

    if(arguments.size()!=3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have three arguments";
    }

    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->source_location=function.source_location();
    t->source_location.set("user-provided", true);
    t->source_location.set_property_class(ID_assertion);
    t->source_location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier==CPROVER_PREFIX "fence")
  {
    if(arguments.size()<1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least one argument";
    }

    goto_programt::targett t=dest.add_instruction(OTHER);
    t->source_location=function.source_location();
    t->code.set(ID_statement, ID_fence);

    forall_expr(it, arguments)
    {
      const irep_idt kind=get_string_constant(*it);
      t->code.set(kind, true);
    }
  }
  else if(identifier=="__builtin_prefetch")
  {
    // does nothing
  }
  else if(identifier=="__builtin_unreachable")
  {
    // says something like assert(false);
  }
  else if(identifier==ID_gcc_builtin_va_arg)
  {
    // This does two things.
    // 1) Move list pointer to next argument.
    //    Done by gcc_builtin_va_arg_next.
    // 2) Return value of argument.
    //    This is just dereferencing.

    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }
    
    exprt list_arg=make_va_list(arguments[0]);
    
    {
      side_effect_exprt rhs(ID_gcc_builtin_va_arg_next, list_arg.type());
      rhs.copy_to_operands(list_arg);
      rhs.set(ID_C_va_arg_type, to_code_type(function.type()).return_type());
      goto_programt::targett t1=dest.add_instruction(ASSIGN);
      t1->source_location=function.source_location();
      t1->code=code_assignt(list_arg, rhs);
    }

    if(lhs.is_not_nil())
    {
      typet t=pointer_typet();
      t.subtype()=lhs.type();
      dereference_exprt rhs(lhs.type());
      rhs.op0()=typecast_exprt(list_arg, t);
      rhs.add_source_location()=function.source_location();
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, rhs);
    }
  }
  else if(identifier=="__builtin_va_copy")
  {
    if(arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have two arguments";
    }
    
    exprt dest_expr=make_va_list(arguments[0]);
    exprt src_expr=typecast_exprt(arguments[1], dest_expr.type());

    if(!is_lvalue(dest_expr))
    {
      err_location(dest_expr);
      throw "va_copy argument expected to be lvalue";
    }    
    
    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->source_location=function.source_location();
    t->code=code_assignt(dest_expr, src_expr);
  }
  else if(identifier=="__builtin_va_start")
  {
    // Set the list argument to be the address of the
    // parameter argument.
    if(arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have two arguments";
    }
    
    exprt dest_expr=make_va_list(arguments[0]);
    exprt src_expr=typecast_exprt(
      address_of_exprt(arguments[1]), dest_expr.type());

    if(!is_lvalue(dest_expr))
    {
      err_location(dest_expr);
      throw "va_start argument expected to be lvalue";
    }    
    
    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->source_location=function.source_location();
    t->code=code_assignt(dest_expr, src_expr);
  }
  else if(identifier=="__builtin_va_end")
  {
    // Invalidates the argument. We do so by setting it to NULL.
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }
    
    exprt dest_expr=make_va_list(arguments[0]);
    
    if(!is_lvalue(dest_expr))
    {
      err_location(dest_expr);
      throw "va_end argument expected to be lvalue";
    }    

    // our __builtin_va_list is a pointer
    if(ns.follow(dest_expr.type()).id()==ID_pointer)
    {
      goto_programt::targett t=dest.add_instruction(ASSIGN);
      t->source_location=function.source_location();
      t->code=code_assignt(dest_expr, gen_zero(dest_expr.type()));
    }
  }
  else if(identifier=="__sync_fetch_and_add" ||
          identifier=="__sync_fetch_and_sub" ||
          identifier=="__sync_fetch_and_or" ||
          identifier=="__sync_fetch_and_and" ||
          identifier=="__sync_fetch_and_xor" ||
          identifier=="__sync_fetch_and_nand")
  {
    // type __sync_fetch_and_OP(type *ptr, type value, ...)
    // { tmp = *ptr; *ptr OP= value; return tmp; }

    if(arguments.size()<2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least two arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }
    
    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }
    
    irep_idt op_id=
      identifier=="__sync_fetch_and_add"?ID_plus:
      identifier=="__sync_fetch_and_sub"?ID_minus:
      identifier=="__sync_fetch_and_or"?ID_bitor:
      identifier=="__sync_fetch_and_and"?ID_bitand:
      identifier=="__sync_fetch_and_xor"?ID_bitxor:
      identifier=="__sync_fetch_and_nand"?ID_bitnand:
      ID_nil;
    
    // build *ptr=*ptr OP arguments[1];
    binary_exprt op_expr(deref_ptr, op_id, arguments[1], deref_ptr.type());
    if(op_expr.op1().type()!=op_expr.type())
      op_expr.op1().make_typecast(op_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, op_expr);
    
    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);

    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_add_and_fetch" ||
          identifier=="__sync_sub_and_fetch" ||
          identifier=="__sync_or_and_fetch" ||
          identifier=="__sync_and_and_fetch" ||
          identifier=="__sync_xor_and_fetch" ||
          identifier=="__sync_nand_and_fetch")
  {
    // type __sync_OP_and_fetch (type *ptr, type value, ...)
    // { *ptr OP= value; return *ptr; }

    if(arguments.size()<2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least two arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }
    
    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    irep_idt op_id=
      identifier=="__sync_add_and_fetch"?ID_plus:
      identifier=="__sync_sub_and_fetch"?ID_minus:
      identifier=="__sync_or_and_fetch"?ID_bitor:
      identifier=="__sync_and_and_fetch"?ID_bitand:
      identifier=="__sync_xor_and_fetch"?ID_bitxor:
      identifier=="__sync_nand_and_fetch"?ID_bitnand:
      ID_nil;
    
    // build *ptr=*ptr OP arguments[1];
    binary_exprt op_expr(deref_ptr, op_id, arguments[1], deref_ptr.type());
    if(op_expr.op1().type()!=op_expr.type())
      op_expr.op1().make_typecast(op_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, op_expr);
    
    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }

    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);
    
    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_bool_compare_and_swap")
  {
    // These builtins perform an atomic compare and swap. That is, if the
    // current value of *ptr is oldval, then write newval into *ptr.  The
    // "bool" version returns true if the comparison is successful and
    // newval was written.  The "val" version returns the contents of *ptr
    // before the operation.

    // These are type-polymorphic, which makes it hard to put
    // them into ansi-c/library.

    // bool __sync_bool_compare_and_swap (type *ptr, type oldval, type newval, ...)
    
    if(arguments.size()<3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least three arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    // build *ptr==oldval    
    equal_exprt equal(deref_ptr, arguments[1]);
    if(equal.op1().type()!=equal.op0().type())
      equal.op1().make_typecast(equal.op0().type());
      
    if(lhs.is_not_nil())
    {
      // return *ptr==oldval
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, equal);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }
    
    // build (*ptr==oldval)?newval:*ptr    
    if_exprt if_expr(equal, arguments[2], deref_ptr, deref_ptr.type());
    if(if_expr.op1().type()!=if_expr.type())
      if_expr.op1().make_typecast(if_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, if_expr);
    
    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);
    
    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_val_compare_and_swap")
  {
    // type __sync_val_compare_and_swap (type *ptr, type oldval, type newval, ...)
    if(arguments.size()<3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least three arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->source_location=function.source_location();

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->source_location=function.source_location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }
    
    // build *ptr==oldval    
    equal_exprt equal(deref_ptr, arguments[1]);
    if(equal.op1().type()!=equal.op0().type())
      equal.op1().make_typecast(equal.op0().type());
      
    // build (*ptr==oldval)?newval:*ptr    
    if_exprt if_expr(equal, arguments[2], deref_ptr, deref_ptr.type());
    if(if_expr.op1().type()!=if_expr.type())
      if_expr.op1().make_typecast(if_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->source_location=function.source_location();
    t3->code=code_assignt(deref_ptr, if_expr);
    
    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->source_location=function.source_location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);
    
    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->source_location=function.source_location();
  }
  else if(identifier=="__sync_lock_test_and_set")
  {
    // type __sync_lock_test_and_set (type *ptr, type value, ...)
    
    // This builtin, as described by Intel, is not a traditional
    // test-and-set operation, but rather an atomic exchange operation. 
    // It writes value into *ptr, and returns the previous contents of
    // *ptr.  Many targets have only minimal support for such locks, and
    // do not support a full exchange operation.  In this case, a target
    // may support reduced functionality here by which the only valid
    // value to store is the immediate constant 1.  The exact value
    // actually stored in *ptr is implementation defined.
  }
  else if(identifier=="__sync_lock_release")
  {
    // This builtin is not a full barrier, but rather an acquire barrier.
    // This means that references after the builtin cannot move to (or be
    // speculated to) before the builtin, but previous memory stores may
    // not be globally visible yet, and previous memory loads may not yet
    // be satisfied.

    // void __sync_lock_release (type *ptr, ...)
  }
  else
  {
    do_function_call_symbol(*symbol);

    // insert function call
    code_function_callt function_call;
    function_call.lhs()=lhs;
    function_call.function()=function;
    function_call.arguments()=arguments;
    function_call.add_source_location()=function.source_location();

    copy(function_call, FUNCTION_CALL, dest);
  }
}
