/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <numeric>
#include <set>
#include <stack>

#include <util/string2int.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/i2string.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>

#include "java_types.h"
#include "java_bytecode_convert.h"
#include "java_bytecode_vtable.h"
#include "bytecode_info.h"

namespace {
class patternt
{
public:
  explicit inline patternt(const char *_p):p(_p)
  {
  }

  // match with '?'  
  friend bool operator==(const irep_idt &what, const patternt &pattern)
  {
    for(unsigned i=0; i<what.size(); i++)
      if(pattern.p[i]==0)
        return false;
      else if(pattern.p[i]!='?' && pattern.p[i]!=what[i])
        return false;

    return pattern.p[what.size()]==0;
  }

protected:
  const char *p;
};

class java_bytecode_convertt:public messaget
{
public:
  java_bytecode_convertt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table)
  {
  }

  void operator()(const java_bytecode_parse_treet &parse_tree)
  {
    if(parse_tree.loading_successful)
      convert(parse_tree.parsed_class);
    else
      generate_class_stub(parse_tree.parsed_class.name);
  }

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::fieldt fieldt;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  typedef methodt::instructionst instructionst;

protected:
  symbol_tablet &symbol_table;

  irep_idt current_method;
  unsigned number_of_parameters;

  // JVM local variables
  symbol_exprt &variable(
    std::map<irep_idt, symbol_exprt> &variables,
    const exprt &arg,
    char type_char)
  {
    irep_idt number=to_constant_expr(arg).get_value();
    
    std::string prefix=(safe_string2unsigned(id2string(number))<number_of_parameters)?"arg":"local";
    irep_idt base_name=prefix+id2string(number)+type_char;
    irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);

    const std::map<irep_idt, symbol_exprt>::iterator variable=
      variables.find(identifier);

    if(variables.end() != variable)
    {
      symbol_exprt &cached(variable->second);
      if(!is_reference_type(type_char))
        cached.type() = java_type_from_char(type_char);
      return cached;
    }

    symbol_exprt result(identifier, java_type_from_char(type_char));
    result.set(ID_C_base_name, base_name);
    std::pair<std::map<irep_idt, symbol_exprt>::iterator, bool> it(variables.insert(std::make_pair(identifier, result)));
    assert(it.second);

    return it.first->second;
  }

  // temporary variables
  unsigned tmp_counter;

  symbol_exprt tmp_variable(const typet &type)
  {
    irep_idt base_name="tmp"+i2string(tmp_counter++);
    irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);
    symbol_exprt result(identifier, type);
    result.set(ID_C_base_name, base_name);
    return result;
  }

  // JVM program locations
  irep_idt label(const irep_idt &address)
  {
    return "pc"+id2string(address);
  }

  // JVM Stack
  typedef std::vector<exprt> stackt;
  stackt stack;

  exprt::operandst pop(unsigned n)
  {
    if(stack.size()<n)
      throw "malformed bytecode (pop too high)";

    exprt::operandst operands;
    operands.resize(n);
    for(unsigned i=0; i<n; i++)
      operands[i]=stack[stack.size()-n+i];

    stack.resize(stack.size()-n);
    return operands;
  }

  void push(const exprt::operandst &o)
  {
    stack.resize(stack.size()+o.size());

    for(unsigned i=0; i<o.size(); i++)
      stack[stack.size()-o.size()+i]=o[i];
  }

  // conversion
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const fieldt &f);
  void convert(symbolt &class_symbol, const methodt &m);
  void convert(const instructiont &i);
  typet convert(const typet &type);

  codet convert_instructions(
    const instructionst &, const code_typet &);

  static const bytecode_infot &get_bytecode_info(const irep_idt &statement);
  
  void generate_class_stub(const irep_idt &class_name);
};
}

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::convert(const classt &c)
{
  class_typet class_type;

  class_type.set_tag(c.name);
  class_type.set(ID_base_name, c.name);

  if(!c.extends.empty())
  {
    symbol_typet base("java::"+id2string(c.extends));
    class_type.add_base(base);
    class_typet::componentt base_class_field;
    base_class_field.type()=base;
    base_class_field.set_name("@"+id2string(c.extends));
    base_class_field.set_base_name("@"+id2string(c.extends));
    base_class_field.set_pretty_name("@"+id2string(c.extends));
    class_type.components().push_back(base_class_field);
  }

  #if 0
  irept &impl=class_type.add(ID_interfaces);
  const std::list<irep_idt> &ifc=c.implements;

  for(std::list<irep_idt>::const_iterator it=ifc.begin();
      it!=ifc.end(); ++it)
  {
    const irept base=make_base(*it);
    class_type.bases().push_back(base); // TODO: Useful?
    impl.get_sub().push_back(base);
  }
  #endif

  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name=c.name;
  new_symbol.pretty_name=c.name;
  new_symbol.name="java::"+id2string(c.name);
  class_type.set(ID_name, new_symbol.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  new_symbol.is_type=true;
  
  symbolt *class_symbol;
  
  // add before we do members
  if(symbol_table.move(new_symbol, class_symbol))
    throw "failed to add class symbol "+id2string(new_symbol.name);

  // now do members  
  for(classt::fieldst::const_iterator
      it=c.fields.begin();
      it!=c.fields.end();
      it++)
    convert(*class_symbol, *it);

  for(classt::methodst::const_iterator
      it=c.methods.begin();
      it!=c.methods.end();
      it++)
    convert(*class_symbol, *it);

  // create the virtual table
  create_vtable_symbol(symbol_table, *class_symbol);

  // is this a root class?
  if(c.extends.empty())
    create_vtable_pointer(*class_symbol);
}

/*******************************************************************\

Function: java_bytecode_convertt::generate_class_stub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::generate_class_stub(const irep_idt &class_name)
{
  class_typet class_type;

  class_type.set_tag(class_name);
  class_type.set(ID_base_name, class_name);

  class_type.set(ID_incomplete_class, true);

  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name=class_name;
  new_symbol.pretty_name=class_name;
  new_symbol.name="java::"+id2string(class_name);
  class_type.set(ID_name, new_symbol.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  new_symbol.is_type=true;
  
  symbolt *class_symbol;
  
  if(symbol_table.move(new_symbol, class_symbol))
    throw "failed to add stub class symbol "+id2string(new_symbol.name);

  // create the virtual table
  create_vtable_symbol(symbol_table, *class_symbol);

  // create vtable pointer
  create_vtable_pointer(*class_symbol);
}

namespace {

const size_t SLOTS_PER_INTEGER(1u);
const size_t INTEGER_WIDTH(64u);
size_t count_slots(const size_t value, const code_typet::parametert &param)
{
  const unsigned int width(param.type().get_unsigned_int(ID_width));
  return value + SLOTS_PER_INTEGER + width / INTEGER_WIDTH;
}

size_t get_variable_slots(const code_typet::parametert &param)
{
  return count_slots(0, param);
}

size_t count_java_parameter_slots(const code_typet::parameterst &p)
{
  return std::accumulate(p.begin(), p.end(), 0, &count_slots);
}

bool is_contructor(const class_typet::methodt &method)
{
  const std::string &name(id2string(method.get_name()));
  const std::string::size_type &npos(std::string::npos);
  return npos != name.find("<init>") || npos != name.find("<clinit>");
}

void cast_if_necessary(binary_relation_exprt &condition)
{
  exprt &lhs(condition.lhs());
  exprt &rhs(condition.rhs());
  const typet &lhs_type(lhs.type());
  if(lhs_type == rhs.type()) return;
  rhs = typecast_exprt(rhs, lhs_type);
}
}

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::convert(
  symbolt &class_symbol,
  const methodt &m)
{
  class_typet &class_type=to_class_type(class_symbol.type);

  typet member_type=java_type_from_string(m.signature);

  assert(member_type.id()==ID_code);

  const irep_idt method_identifier=
    id2string(class_symbol.name)+"."+id2string(m.name)+":"+m.signature;

  code_typet &code_type=to_code_type(member_type);
  code_typet::parameterst &parameters=code_type.parameters();

  // do we need to add 'this' as a parameter?
  if(!m.is_static)
  {
    code_typet::parametert this_p;
    const empty_typet empty;
    const pointer_typet object_ref_type(empty);
    this_p.type()=object_ref_type;
    this_p.set(ID_C_this, true);
    parameters.insert(parameters.begin(), this_p);
  }

  // assign names to parameters
  for(size_t i=0, param_index=0;
      i < parameters.size(); ++i)
  {
    irep_idt base_name="arg"+i2string(param_index);
    const typet &type=parameters[i].type();
    irep_idt identifier=id2string(method_identifier)+"::"+id2string(base_name)+java_char_from_type(type);
    parameters[i].set_base_name(base_name);
    parameters[i].set_identifier(identifier);

    // add to symbol table
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name=base_name;
    parameter_symbol.mode=ID_java;
    parameter_symbol.name=identifier;
    parameter_symbol.type=parameters[i].type();
    symbol_table.add(parameter_symbol);
    param_index+=get_variable_slots(parameters[i]);
  }

  class_type.methods().push_back(class_typet::methodt());
  class_typet::methodt &method=class_type.methods().back();

  method.set_base_name(m.base_name);
  method.set_name(method_identifier);

  const bool is_virtual=!m.is_static && !m.is_final;

  method.set(ID_abstract, m.is_abstract);
  method.set(ID_is_virtual, is_virtual);

  if(is_virtual)
    set_virtual_name(method);

  if(is_contructor(method))
    method.set(ID_constructor, true);

  method.type()=member_type;

  // create method symbol
  symbolt method_symbol;
  method_symbol.mode=ID_java;
  method_symbol.name=method.get_name();
  method_symbol.base_name=method.get_base_name();
  method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                            id2string(method.get_base_name())+"()";
  method_symbol.type=member_type;
  current_method=method_symbol.name;
  number_of_parameters=count_java_parameter_slots(parameters);
  tmp_counter=0;
  method_symbol.value=convert_instructions(m.instructions, code_type);
  symbol_table.add(method_symbol);
}

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::convert(
  symbolt &class_symbol,
  const fieldt &f)
{
  class_typet &class_type=to_class_type(class_symbol.type);

  typet member_type=java_type_from_string(f.signature);

  class_type.components().push_back(class_typet::componentt());
  class_typet::componentt &component=class_type.components().back();

  component.set_name(f.name);
  component.set_base_name(f.name);
  component.type()=member_type;
  
  if(f.is_private)
    component.set_access(ID_private);
  else if(f.is_protected)
    component.set_access(ID_protected);
  else if(f.is_public)
    component.set_access(ID_public);

  // is this a static field?
  if(f.is_static)
  {
    // create the symbol
    symbolt new_symbol;

    new_symbol.is_static_lifetime=true;
    new_symbol.is_lvalue=true;
    new_symbol.is_state_var=true;
    new_symbol.name=id2string(class_symbol.name)+"."+id2string(f.name);
    new_symbol.base_name=f.name;
    new_symbol.type=member_type;
    new_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+id2string(f.name);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;  
    new_symbol.value=gen_zero(member_type);

    if(symbol_table.add(new_symbol))
      throw "failed to add static field symbol";
  }
}

/*******************************************************************\

Function: java_bytecode_convertt::get_bytecode_info

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const bytecode_infot &java_bytecode_convertt::get_bytecode_info(
  const irep_idt &statement)
{
  for(const bytecode_infot *p=bytecode_info; p->mnemonic!=0; p++)
    if(statement==p->mnemonic) return *p;

  throw std::string("failed to find bytecode mnemonic `")+
        id2string(statement)+"'";
}

namespace {

irep_idt get_if_cmp_operator(const irep_idt &stmt)
{
  if(stmt == patternt("if_?cmplt")) return ID_lt;
  if(stmt == patternt("if_?cmple")) return ID_le;
  if(stmt == patternt("if_?cmpgt")) return ID_gt;
  if(stmt == patternt("if_?cmpge")) return ID_ge;
  if(stmt == patternt("if_?cmpeq")) return ID_equal;
  if(stmt == patternt("if_?cmpne")) return ID_notequal;

  throw "Unhandled java comparison instruction";
}

constant_exprt as_number(const mp_integer value, const typet &type)
{
  const unsigned int java_int_width(type.get_unsigned_int(ID_width));
  const std::string significant_bits(integer2string(value, 2));
  std::string binary_width(java_int_width - significant_bits.length(), '0');
  return constant_exprt(binary_width += significant_bits, type);
}

member_exprt to_member(const exprt &pointer, const exprt &fieldref)
{
  symbol_typet class_type(fieldref.get(ID_class));

  exprt pointer2=
    typecast_exprt(pointer, pointer_typet(class_type));
    
  const dereference_exprt obj_deref(pointer2, class_type);

  return member_exprt(
    obj_deref, fieldref.get(ID_component_name), fieldref.type());
}
}

/*******************************************************************\

Function: java_bytecode_convertt::convert_instructions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

codet java_bytecode_convertt::convert_instructions(
  const instructionst &instructions,
  const code_typet &method_type)
{
  // Run a worklist algorithm, assuming that the bytecode has not
  // been tampered with. See "Leroy, X. (2003). Java bytecode
  // verification: algorithms and formalizations. Journal of Automated
  // Reasoning, 30(3-4), 235-269." for a more complete treatment.

  // first pass: get targets and map addresses to instructions
  
  struct converted_instructiont
  {
    converted_instructiont(
      const instructionst::const_iterator &it,
      const codet &_code):source(it), code(_code), done(false)
    {
    }

    instructionst::const_iterator source;
    std::list<unsigned> successors;
    codet code;
    bool done;
  };
  typedef std::map<unsigned, converted_instructiont> address_mapt;
  address_mapt address_map;
  std::set<unsigned> targets;

  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
  {
    std::pair<address_mapt::iterator, bool> a_entry=
      address_map.insert(std::make_pair(
          i_it->address,
          converted_instructiont(i_it, code_skipt())));
    assert(a_entry.second);
    // addresses are strictly increasing, hence we must have inserted
    // a new maximal key
    assert(a_entry.first==--address_map.end());

    if(i_it->statement!="goto")
    {
      instructionst::const_iterator next=i_it;
      if(++next!=instructions.end())
        a_entry.first->second.successors.push_back(next->address);
    }

    if(i_it->statement=="goto" ||
       i_it->statement==patternt("if_?cmp??") ||
       i_it->statement==patternt("if??") ||
       i_it->statement=="ifnonnull" ||
       i_it->statement=="ifnull")
    {
      assert(!i_it->args.empty());
      const unsigned target=safe_string2unsigned(
        id2string(to_constant_expr(i_it->args[0]).get_value()));
      targets.insert(target);
      a_entry.first->second.successors.push_back(target);
    }
    else if(i_it->statement=="tableswitch" ||
            i_it->statement=="lookupswitch")
    {
      bool is_label=true;
      for(instructiont::argst::const_iterator
          a_it=i_it->args.begin();
          a_it!=i_it->args.end();
          a_it++, is_label=!is_label)
      {
        if(is_label)
        {
          const unsigned target=safe_string2unsigned(
            id2string(to_constant_expr(*a_it).get_value()));
          targets.insert(target);
          a_entry.first->second.successors.push_back(target);
        }
      }
    }
  }

  std::map<irep_idt, symbol_exprt> loc_vars;

  std::set<unsigned> working_set;
  if(!instructions.empty())
    working_set.insert(instructions.front().address);

  while(!working_set.empty())
  {
    std::set<unsigned>::iterator cur=working_set.begin();
    address_mapt::iterator a_it=address_map.find(*cur);
    assert(a_it!=address_map.end());
    working_set.erase(cur);

    if(a_it->second.done) continue;
    working_set.insert(a_it->second.successors.begin(),
                       a_it->second.successors.end());

    instructionst::const_iterator i_it=a_it->second.source;
    codet &c=a_it->second.code;

    irep_idt statement=i_it->statement;
    exprt arg0=i_it->args.size()>=1?i_it->args[0]:nil_exprt();
    exprt arg1=i_it->args.size()>=2?i_it->args[1]:nil_exprt();

    const bytecode_infot &bytecode_info=get_bytecode_info(statement);

    // deal with _idx suffixes
    if(statement.size()>=2 &&
       statement[statement.size()-2]=='_' &&
       isdigit(statement[statement.size()-1]))
    {
      arg0=constant_exprt(
        std::string(id2string(statement), statement.size()-1, 1),
        integer_typet());
      statement=std::string(id2string(statement), 0, statement.size()-2);
    }

    exprt::operandst op=pop(bytecode_info.pop);
    exprt::operandst results;
    results.resize(bytecode_info.push, nil_exprt());

    if(statement=="aconst_null")
    {
      assert(results.size()==1);
      results[0]=gen_zero(java_reference_type(void_typet()));
    }
    else if(statement=="athrow")
    {
      assert(op.size()==1 && results.size()==1);
      side_effect_expr_throwt throw_expr;
      throw_expr.copy_to_operands(op[0]);
      c=code_expressiont(throw_expr);
      results[0]=op[0];
    }
    else if(statement=="checkcast")
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=op[0];
    }
    else if(statement=="invokedynamic")
    {
      // not used in Java, will need to investigate what it does
    }
    else if(statement=="invokeinterface" ||
            statement=="invokespecial" ||
            statement=="invokevirtual" ||
            statement=="invokestatic")
    {
      const bool use_this(statement != "invokestatic");
      const bool is_virtual(
        statement == "invokevirtual" || statement == "invokeinterface");
      
      code_typet &code_type=to_code_type(arg0.type());
      code_typet::parameterst &parameters(code_type.parameters());

      if(use_this)
      {
        if(parameters.empty() || !parameters[0].get_bool(ID_C_this))
        {
          const empty_typet empty;
          pointer_typet object_ref_type(empty);
          code_typet::parametert this_p(object_ref_type);
          this_p.set(ID_C_this, true);
          parameters.insert(parameters.begin(), this_p);
        }
      }

      code_function_callt call;
      call.add_source_location()=i_it->source_location;
      call.arguments() = pop(parameters.size());

      const typet &return_type=code_type.return_type();

      if(ID_empty != return_type.id())
      {
        call.lhs() = tmp_variable(return_type);
        results.resize(1);
        results[0] = call.lhs();
      }

      if(is_virtual)
      {
#if 0
        const exprt &this_arg=call.arguments().front();
        call.function() = make_vtable_function(arg0, this_arg);
#else
        call.function() = arg0;
#endif
      }
      else
        call.function() = arg0;

      call.function().add_source_location()=i_it->source_location;
      c = call;
    }
    else if(statement=="return")
    {
      assert(op.empty() && results.empty());
      c=code_returnt();
    }
    else if(statement==patternt("?return"))
    {
      assert(op.size()==1 && results.empty());
      // return values are promoted
      exprt retval=java_bytecode_promotion(op[0]);
      c=code_returnt(retval);
    }
    else if(statement==patternt("?astore"))
    {
      assert(op.size()==3 && results.empty());
      
      exprt pointer=
        typecast_exprt(op[0], java_array_type(statement[0]));

      const dereference_exprt deref(pointer, pointer.type().subtype());
      assert(pointer.type().subtype().id()==ID_struct);
      const struct_typet &struct_type=to_struct_type(pointer.type().subtype());
      assert(struct_type.components().size()==2);

      const member_exprt data_ptr(
        deref, struct_type.components()[1].get_name(), struct_type.components()[1].type());

      plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
      typet element_type=data_ptr.type().subtype();
      const dereference_exprt element(data_plus_offset, element_type);

      c=code_assignt(element, op[2]);
    }
    else if(statement==patternt("?store"))
    {
      // store value into some local variable
      assert(op.size()==1 && results.empty());

      symbol_exprt var=variable(loc_vars, arg0, statement[0]);

      const bool is_array('a' == statement[0]);
      
      if(is_array)
        var.type()=op[0].type();

      c=code_assignt(var, op[0]);
    }
    else if(statement==patternt("?aload"))
    {
      assert(op.size() == 2 && results.size() == 1);

      exprt pointer=
        typecast_exprt(op[0], java_array_type(statement[0]));

      const dereference_exprt deref(pointer, pointer.type().subtype());
      const struct_typet &struct_type=to_struct_type(pointer.type().subtype());
      assert(struct_type.components().size()==2);

      const member_exprt data_ptr(
        deref, struct_type.components()[1].get_name(), struct_type.components()[1].type());

      plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
      typet element_type=data_ptr.type().subtype();
      dereference_exprt element(data_plus_offset, element_type);

      results[0]=java_bytecode_promotion(element);
    }
    else if(statement==patternt("?load"))
    {
      // load a value from a local variable
      results[0]=variable(loc_vars, arg0, statement[0]);
    }
    else if(statement=="ldc" || statement=="ldc_w" ||
            statement=="ldc2" || statement=="ldc2_w")
    {
      assert(op.empty() && results.size()==1);
      results[0]=arg0;
    }
    else if(statement=="goto" || statement=="goto_w")
    {
      assert(op.empty() && results.empty());
      irep_idt number=to_constant_expr(arg0).get_value();
      code_gotot code_goto(label(number));
      c=code_goto;
    }
    else if(statement=="iconst_m1")
    {
      assert(results.size()==1);
      results[0]=from_integer(-1, java_int_type());
    }
    else if(statement==patternt("?const"))
    {
      assert(results.size() == 1);

      const char type_char=statement[0];
      const bool is_double('d' == type_char);
      const bool is_float('f' == type_char);

      if(is_double || is_float)
      {
        const ieee_float_spect spec(
            is_float ?
                ieee_float_spect::single_precision() :
                ieee_float_spect::double_precision());

        ieee_floatt value(spec);
        const typet &arg_type(arg0.type());
        if(ID_integer == arg_type.id())
          value.from_integer(arg0.get_int(ID_value));
        else
          value.from_expr(to_constant_expr(arg0));

        results[0] = value.to_expr();
      }
      else
      {
        const unsigned int value(arg0.get_unsigned_int(ID_value));
        const typet type=java_type_from_char(statement[0]);
        results[0] = as_number(value, type);
      }
    }
    else if(statement==patternt("?ipush"))
    {
      assert(results.size()==1);
      results[0]=typecast_exprt(arg0, java_int_type());
    }
    else if(statement==patternt("if_?cmp??"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==2 && results.empty());

      code_ifthenelset code_branch;
      const irep_idt cmp_op=get_if_cmp_operator(statement);
      
      binary_relation_exprt condition(op[0], cmp_op, op[1]);
      cast_if_necessary(condition);
      code_branch.cond()=condition;
      code_branch.then_case()=code_gotot(label(number));
      
      c=code_branch;
    }
    else if(statement==patternt("if??"))
    {
      const irep_idt id=
        statement=="ifeq"?ID_equal:
        statement=="ifne"?ID_notequal:
        statement=="iflt"?ID_lt:
        statement=="ifge"?ID_ge:
        statement=="ifgt"?ID_gt:
        statement=="ifle"?ID_le:
        (assert(false), "");

      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], id, gen_zero(op[0].type()));
      code_branch.then_case()=code_gotot(label(number));
      c=code_branch;
    }
    else if(statement==patternt("ifnonnull"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      const typecast_exprt lhs(op[0], pointer_typet());
      const exprt rhs(gen_zero(lhs.type()));
      code_branch.cond()=binary_relation_exprt(lhs, ID_notequal, rhs);
      code_branch.then_case()=code_gotot(label(number));
      c=code_branch;
    }
    else if(statement==patternt("ifnull"))
    {
      assert(op.size()==1 && results.empty());
      irep_idt number=to_constant_expr(arg0).get_value();
      code_ifthenelset code_branch;
      const typecast_exprt lhs(op[0], pointer_typet());
      const exprt rhs(gen_zero(lhs.type()));
      code_branch.cond()=binary_relation_exprt(lhs, ID_equal, rhs);
      code_branch.then_case()=code_gotot(label(number));
      c=code_branch;
    }
    else if(statement=="iinc")
    {
      code_assignt code_assign;
      code_assign.lhs()=variable(loc_vars, arg0, 'i');
      code_assign.rhs()=plus_exprt(variable(loc_vars, arg0, 'i'), typecast_exprt(arg1, java_int_type()));
      c=code_assign;
    }
    else if(statement==patternt("?xor"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitxor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?or"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?and"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitand_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shl"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=shl_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shr"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=ashr_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?ushr"))
    {
      assert(op.size()==2 && results.size()==1);
      const typet type(java_type_from_char(statement[0]));

      const unsigned int width(type.get_unsigned_int(ID_width));
      typet target=unsigned_long_int_type();
      target.set(ID_width, width);

      const typecast_exprt lhs(op[0], target);
      const typecast_exprt rhs(op[1], target);

      results[0]=lshr_exprt(lhs, rhs);
    }
    else if(statement==patternt("?add"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=plus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?sub"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=minus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?div"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=div_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?mul"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=mult_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?neg"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=unary_minus_exprt(op[0], op[0].type());
    }
    else if(statement==patternt("?rem"))
    {
      assert(op.size()==2 && results.size()==1);
      if(statement=="frem" || statement=="drem")
        results[0]=rem_exprt(op[0], op[1]);
      else
        results[0]=mod_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?cmp"))
    {
      assert(op.size() == 2 && results.size() == 1);

      // The integer result on the stack is:
      //  0 if op[0] equals op[1]
      // -1 if op[0] is less than op[1]
      //  1 if op[0] is greater than op[1]

      const typet t=java_int_type();

      results[0]=
        if_exprt(binary_relation_exprt(op[0], ID_equal, op[1]), gen_zero(t),
        if_exprt(binary_relation_exprt(op[0], ID_gt, op[1]), from_integer(1, t),
        from_integer(-1, t)));
    }
    else if(statement==patternt("?cmp?"))
    {
      assert(op.size()==2 && results.size()==1);
      const floatbv_typet type(to_floatbv_type(java_type_from_char(statement[0])));
      const ieee_float_spect spec(type);
      const ieee_floatt nan(ieee_floatt::NaN(spec));
      const constant_exprt nan_expr(nan.to_expr());
      const int nan_value(statement[4] == 'l' ? -1 : 1);
      const typet result_type(java_int_type());
      const exprt nan_result(from_integer(nan_value, result_type));

      // (value1 == NaN || value2 == NaN) ? nan_value : value1  < value2 ? -1 : value2 < value1  1 ? 1 : 0;
      // (value1 == NaN || value2 == NaN) ? nan_value : value1 == value2 ? 0  : value1 < value2 -1 ? 1 : 0;

      results[0]=
        if_exprt(or_exprt(ieee_float_equal_exprt(nan_expr, op[0]), ieee_float_equal_exprt(nan_expr, op[1])), nan_result,
        if_exprt(ieee_float_equal_exprt(op[0], op[1]), gen_zero(result_type),
        if_exprt(binary_relation_exprt(op[0], ID_lt, op[1]), from_integer(-1, result_type), from_integer(1, result_type))));
    }
    else if(statement==patternt("?cmpl"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=binary_relation_exprt(op[0], ID_lt, op[1]);
    }
    else if(statement=="dup")
    {
      assert(op.size()==1 && results.size()==2);
      results[0]=results[1]=op[0];
    }
    else if(statement=="dup_x1")
    {
      assert(op.size()==2 && results.size()==3);
      results[0]=op[1];
      results[1]=op[0];
      results[2]=op[1];
    }
    else if(statement=="dconst")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement=="fconst")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement=="getfield")
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=to_member(op[0], arg0);
    }
    else if(statement=="getstatic")
    {
      assert(op.empty() && results.size()==1);
      symbol_exprt symbol_expr(arg0.type());
      symbol_expr.set_identifier(arg0.get_string(ID_class)+"."+arg0.get_string(ID_component_name));
      results[0]=symbol_expr;
    }
    else if(statement=="putfield")
    {
      assert(op.size()==2 && results.size()==0);
      c = code_assignt(to_member(op[0], arg0), op[1]);
    }
    else if(statement=="putstatic")
    {
      assert(op.size()==1 && results.empty());
      symbol_exprt symbol_expr(arg0.type());
      symbol_expr.set_identifier(arg0.get_string(ID_class)+"."+arg0.get_string(ID_component_name));
      c=code_assignt(symbol_expr, op[0]);
    }
    else if(statement==patternt("?2?")) // i2c etc.
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_type_from_char(statement[2]));
    }
    else if(statement=="new")
    {
      // use temporary since the stack symbol might get duplicated
      assert(op.empty() && results.size()==1);
      const pointer_typet ref_type(arg0.type());
      exprt java_new_expr=side_effect_exprt(ID_java_new, ref_type);

      if(!i_it->source_location.get_line().empty())
        java_new_expr.add_source_location()=i_it->source_location;

      const exprt tmp=tmp_variable(ref_type);
      c=code_assignt(tmp, java_new_expr);
      results[0]=tmp;
    }
    else if(statement=="newarray" ||
            statement=="anewarray")
    {
      // the op is the array size
      assert(op.size()==1 && results.size()==1);

      typet element_type;
      
      if(statement=="newarray")
      {
        irep_idt id=arg0.type().id();

        if(id==ID_bool)
          element_type=java_byte_type();
        else if(id==ID_char)
          element_type=java_char_type();
        else if(id==ID_float)
          element_type=java_float_type();
        else if(id==ID_double)
          element_type=java_double_type();
        else if(id==ID_byte)
          element_type=java_byte_type();
        else if(id==ID_short)
          element_type=java_short_type();
        else if(id==ID_int)
          element_type=java_int_type();
        else if(id==ID_long)
          element_type=java_long_type();
      }
      else
        element_type=java_reference_type(empty_typet());

      const typet ref_type=java_array_type(element_type, 1);

      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.copy_to_operands(op[0]);

      if(!i_it->source_location.get_line().empty())
        java_new_array.add_source_location()=i_it->source_location;

      const exprt tmp=tmp_variable(ref_type);
      c=code_assignt(tmp, java_new_array);
      results[0]=tmp;
    }
    else if(statement=="multianewarray")
    {
      // The first argument is the type, the second argument is the dimension.
      // The size of each dimension is on the stack.
      irep_idt number=to_constant_expr(arg1).get_value();
      unsigned dimension=safe_c_str2unsigned(number.c_str());

      op=pop(dimension);
      assert(results.size()==1);

      const typet ref_type=java_array_type(arg0.type(), dimension);

      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.operands()=op;

      if(!i_it->source_location.get_line().empty())
        java_new_array.add_source_location()=i_it->source_location;

      const exprt tmp=tmp_variable(ref_type);
      c=code_assignt(tmp, java_new_array);
      results[0]=tmp;
    }
    else if(statement=="arraylength")
    {
      assert(op.size()==1 && results.size()==1);

      exprt pointer=
        typecast_exprt(op[0], java_array_type(statement[0]));

      const dereference_exprt array(pointer, pointer.type().subtype());
      assert(pointer.type().subtype().id()==ID_struct);
      const struct_typet &struct_type=to_struct_type(pointer.type().subtype());
      assert(struct_type.components().size()==2);

      const member_exprt length(
        array, struct_type.components()[0].get_name(), struct_type.components()[0].type());

      results[0]=length;
    }
    else if(statement=="tableswitch" ||
            statement=="lookupswitch")
    {
      assert(op.size()==1 && results.size()==0);

      // we turn into switch-case
      code_switcht code_switch;
      code_switch.value()=op[0];
      code_blockt code_block;

      bool is_label=true;
      for(instructiont::argst::const_iterator
          a_it=i_it->args.begin();
          a_it!=i_it->args.end();
          a_it++, is_label=!is_label)
      {
        if(is_label)
        {
          code_switch_caset code_case;

          irep_idt number=to_constant_expr(*a_it).get_value();
          code_case.code()=code_gotot(label(number));
        
          if(a_it==i_it->args.begin())
            code_case.set_default();
          else
          {
            instructiont::argst::const_iterator prev=a_it;
            prev--;
            code_case.case_op()=typecast_exprt(*prev, op[0].type());
          }
          
          code_block.add(code_case);
        }
      }
      
      code_switch.body()=code_block;
      c=code_switch;
    }
    else if(statement=="pop" || statement=="pop2")
    {
      // these are skips
      c=code_skipt();
    }
    else
    {
      c=codet(statement);
      c.operands()=op;
    }
    
    if(!i_it->source_location.get_line().empty())
      c.add_source_location()=i_it->source_location;

    push(results);

    a_it->second.done=true;
  }

  // TODO: add exception handlers from exception table
  code_blockt code;

  for(address_mapt::const_iterator it=
      address_map.begin();
      it!=address_map.end();
      ++it)
  {
    const unsigned address=it->first;
    assert(it->first==it->second.source->address);
    const codet &c=it->second.code;

    if(targets.find(address)!=targets.end())
      code.add(code_labelt(label(i2string(address)), c));
    else if(c.get_statement()!=ID_skip)
      code.add(c);
  }

  return code;
}

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet java_bytecode_convertt::convert(const typet &type)
{
  if(type.id()==ID_void)
    return empty_typet();
  else if(type.id()==ID_code)
  {
    code_typet code_type=to_code_type(type); // copy, will change

    code_type.return_type()=convert(code_type.return_type());

    code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      it->type()=convert(it->type());
    }

    return code_type;
  }
  else
    return type;
}

/*******************************************************************\

Function: java_bytecode_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_convert(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  java_bytecode_convertt java_bytecode_convert(
    symbol_table, message_handler);

  try
  {
    java_bytecode_convert(parse_tree);
    return false;
  }

  catch(int)
  {
  }

  catch(const char *e)
  {
    java_bytecode_convert.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    java_bytecode_convert.error() << e << messaget::eom;
  }

  return true;
}
