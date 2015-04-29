/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

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

// http://en.wikipedia.org/wiki/Java_bytecode_instruction_listings

// The 'result_type' is one of the following:
// i  integer
// l  long
// s  short
// b  byte
// c  character
// f  float
// d  double
// z  boolean
// a  reference

struct bytecode_infot
{
  const char *mnemonic;
  unsigned char opcode;
  unsigned pop, push;
  char result_type;
} const bytecode_info[]= {
#include "bytecode_info.inc"
};

class patternt
{
public:
  explicit inline patternt(const char *_p):p(_p)
  {
  }

  const char *p;

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
    convert(parse_tree);
  }

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::membert membert;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  typedef membert::instructionst instructionst;

protected:
  symbol_tablet &symbol_table;
  
  irep_idt current_method;
  unsigned number_of_parameters;
  
  // JVM local variables
  symbol_exprt variable(const exprt &arg, char type_char)
  {
    irep_idt number=to_constant_expr(arg).get_value();
    std::string prefix=(unsafe_string2unsigned(id2string(number))<number_of_parameters)?"arg":"local";
    irep_idt base_name=prefix+id2string(number)+type_char;
    irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);
    symbol_exprt result(identifier, java_type(type_char));
    result.set(ID_C_base_name, base_name);
    return result;
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
  void convert(const java_bytecode_parse_treet &parse_tree);
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const membert &m);
  void convert(const instructiont &i);
  typet convert(const typet &type);
  codet convert_instructions(const instructionst &);  

  static const bytecode_infot &get_bytecode_info(const irep_idt &statement);
};

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::convert(
  const java_bytecode_parse_treet &parse_tree)
{
  for(java_bytecode_parse_treet::classest::const_iterator
      it=parse_tree.classes.begin();
      it!=parse_tree.classes.end();
      it++)
    convert(*it);
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
  
  // produce class symbol
  symbolt new_symbol;
  new_symbol.base_name=c.name;
  new_symbol.pretty_name=c.name;
  new_symbol.name="java::"+id2string(c.name);
  new_symbol.type=class_type;
  new_symbol.mode=ID_java;
  
  for(classt::memberst::const_iterator
      it=c.members.begin();
      it!=c.members.end();
      it++)
    convert(new_symbol, *it);
  
  symbol_table.add(new_symbol);
}

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::convert(
  symbolt &class_symbol,
  const membert &m)
{
  class_typet &class_type=to_class_type(class_symbol.type);
  
  typet member_type=java_type_from_string(m.signature);

  if(member_type.id()==ID_code)
  {
    irep_idt method_identifier=
      id2string(class_symbol.name)+"."+id2string(m.name)+":"+m.signature;

    code_typet &code_type=to_code_type(member_type);
    code_typet::parameterst &parameters=code_type.parameters();
    
    // do we need to add 'this'?
    if(!m.is_static)
    {
      code_typet::parametert this_p;
      symbol_typet class_type(class_symbol.name);
      this_p.set(ID_C_this, true);
      this_p.type()=java_reference_type(class_type);
      parameters.insert(parameters.begin(), this_p);
    }
    
    // assign names to parameters
    for(unsigned i=0; i<parameters.size(); i++)
    {
      irep_idt base_name="arg"+i2string(i);
      irep_idt identifier=id2string(method_identifier)+"::"+id2string(base_name);
      parameters[i].set_base_name(base_name);
      parameters[i].set_identifier(identifier);
      
      // add to symbol table
      symbolt parameter_symbol;
      parameter_symbol.base_name=base_name;
      parameter_symbol.mode=ID_java;
      parameter_symbol.name=identifier;
      parameter_symbol.type=parameters[i].type();
      parameter_symbol.is_lvalue=true;
      parameter_symbol.is_state_var=true;
      symbol_table.add(parameter_symbol);
    }

    class_type.methods().push_back(class_typet::methodt());
    class_typet::methodt &method=class_type.methods().back();
    
    method.set_base_name(m.base_name);
    method.set_name(method_identifier);
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
    number_of_parameters=parameters.size();
    tmp_counter=0;
    method_symbol.value=convert_instructions(m.instructions);
    symbol_table.add(method_symbol);
  }
  else
  {
    class_type.components().push_back(class_typet::componentt());
    class_typet::componentt &component=class_type.components().back();
    
    component.set_name(m.name);
    component.set_base_name(m.base_name);
    component.type()=member_type;
  }
}

/*******************************************************************\

Function: java_bytecode_convertt::get_bytecode_info

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const bytecode_infot &java_bytecode_convertt::get_bytecode_info(const irep_idt &statement)
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
  assert(!"Unhandled java comparison instruction.");
}

constant_exprt as_number(const mp_integer &value, const typet &type)
{
  const unsigned int java_int_width(type.get_unsigned_int(ID_width));
  const std::string significant_bits(integer2string(value, 2));
  std::string binary_width(java_int_width - significant_bits.length(), '0');
  return constant_exprt(binary_width += significant_bits, type);
}

constant_exprt as_int(const mp_integer &value)
{
  return as_number(value, java_int_type());
}

constant_exprt as_width(const size_t width)
{
  return as_int(width);
}

//constant_exprt java_integer_width() {
//  return as_width(32u);
//}

const std::pair<typet, exprt> get_java_type(const irep_idt &type_id)
{
  if(ID_boolean == type_id)
    return std::make_pair(java_boolean_type(), as_width(1));

  if(ID_char == type_id)
    return std::make_pair(java_char_type(), as_width(16));

  if(ID_float == type_id)
    return std::make_pair(java_float_type(), as_width(16));

  if(ID_double == type_id)
    return std::make_pair(java_float_type(), as_width(32));

  if(ID_byte == type_id)
    return std::make_pair(java_byte_type(), as_width(8));

  if(ID_short == type_id)
    return std::make_pair(java_short_type(), as_width(16));

  if(ID_int == type_id)
    return std::make_pair(java_int_type(), as_width(32));

  if(ID_long == type_id)
    return std::make_pair(java_long_type(), as_width(64));

  throw "Unsupported primitive type array";
}

}

/*******************************************************************\

Function: java_bytecode_convertt::convert_instructions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

codet java_bytecode_convertt::convert_instructions(
  const instructionst &instructions)
{
  // first pass: get targets
  
  std::set<irep_idt> targets;
  
  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
  {
    if(i_it->statement=="goto" ||
       i_it->statement==patternt("if_?cmp??") ||
       i_it->statement==patternt("if??") ||
       i_it->statement=="ifnonnull" ||
       i_it->statement=="ifnull")
    {
      assert(!i_it->args.empty());
      targets.insert(label(to_constant_expr(i_it->args[0]).get_value()));
    }
    else if(i_it->statement=="tableswitch")
    {
    }
    else if(i_it->statement=="lookupswitch")
    {
    }
  }

  code_blockt code;

  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
  {
    codet c=code_skipt();
  
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
      bool use_this=statement!="invokestatic";
      bool is_virtual=statement=="invokevirtual";
    
      code_function_callt call;
      
      code_typet code_type=to_code_type(arg0.type());
      code_typet::parameterst &parameters=code_type.parameters();

      // check for 'this'
      if(use_this)
      {
        // does the function have 'this'?
        if(parameters.empty() ||
           !parameters[0].get_bool(ID_C_this))
        {
          // add 'this'
          code_typet::parametert this_p;
          this_p.type()=java_reference_type(typet());
          this_p.set(ID_C_this, true);
          parameters.insert(parameters.begin(), this_p);
        }
      }
      
      // arguments, these all come off the stack
      call.arguments()=pop(parameters.size());

      // return value, goes onto the stack
      const typet &return_type=code_type.return_type();
      if(return_type.id()!=ID_empty)
      {
        call.lhs()=tmp_variable(return_type);
        results.resize(1);
        results[0]=call.lhs();
      }

      if(is_virtual)
      {
        /*
        irep_idt identifier=arg0.get(ID_identifier);
        member_exprt member_expr;
        member_expr.set_component_name(identifier);
        member_expr.type()=pointer_typet(arg0.type());
        member_expr.struct_op()=call.arguments()[0]; // this
        dereference_exprt deref_expr(member_expr, arg0.type());
        call.function()=deref_expr;
        */
        call.function()=arg0;
      }
      else
        call.function()=arg0;
      
      c=call;
    }
    else if(statement=="return")
    {
      assert(op.empty() && results.empty());
      code_returnt code_return;
      c=code_return;
    }
    else if(statement==patternt("?return"))
    {
      assert(op.size()==1 && results.empty());
      code_returnt code_return(op[0]);
      c=code_return;
    }
    else if(statement==patternt("?astore"))
    {
      assert(op.size() == 3 && results.empty());
      const dereference_exprt array(op[0], op[0].type().subtype());
      const typet elem_type(java_type(statement[0]));
      const array_typet array_type(elem_type, exprt());
      const member_exprt data(array, "data", array_type);
      const index_exprt element(data, op[1], elem_type);
      c = code_assignt(element, op[2]);
    }
    else if(statement==patternt("?store"))
    {
      // store value into some local variable
      assert(op.size()==1 && results.empty());
      symbol_exprt var(variable(arg0, statement[0]));
      const bool is_array('a' == statement[0]);
      if (is_array) {
        var.type() = op[0].type();
      }
      c = code_assignt(var, op[0]);
    }
    else if(statement==patternt("?aload"))
    {
      assert(op.size() == 2 && results.size() == 1);
      const dereference_exprt array(op[0], op[0].type().subtype());
      const typet elem_type(java_type(statement[0]));
      const array_typet array_type(elem_type, exprt());
      const member_exprt data(array, "data", array_type);
      const typecast_exprt index(op[1], signed_long_int_type());
      const index_exprt element(data, index, elem_type);
      if(elem_type.get_unsigned_int(ID_width) < 32u) {
        results[0]=typecast_exprt(element, java_int_type());
      } else {
        results[0]=element;
      }
    }
    else if(statement==patternt("?load"))
    {
      // load a value from a local variable
      results[0]=variable(arg0, statement[0]);
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
      const char type_char(statement[0]);
      const bool is_double('d' == type_char);
      const bool is_float('f' == type_char);
      if (is_double || is_float)
      {
        const ieee_float_spect spec(
            is_float ?
                ieee_float_spect::single_precision() :
                ieee_float_spect::double_precision());

        ieee_floatt value(spec);
        const typet &arg_type=arg0.type();

        if(ID_integer == arg_type.id())
          value.from_integer(arg0.get_int(ID_value));
        else
          value.from_expr(to_constant_expr(arg0));

        results[0] = value.to_expr();
      }
      else
      {
        const unsigned int value=arg0.get_unsigned_int(ID_value);
        const typet type=java_type(statement[0]);
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
      const irep_idt cmp_op(get_if_cmp_operator(statement));
      code_branch.cond()=binary_relation_exprt(op[0], cmp_op, op[1]);
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
      code_branch.cond()=binary_relation_exprt(op[0], ID_notequal, gen_zero(java_int_type()));
      code_branch.then_case()=code_gotot(label(number));
      c=code_branch;
    }
    else if(statement==patternt("ifnull"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_equal, gen_zero(java_int_type()));
      code_branch.then_case()=code_gotot(label(number));
      c=code_branch;
    }
    else if(statement=="iinc")
    {
      code_assignt code_assign;
      code_assign.lhs()=variable(arg0, 'i');
      code_assign.rhs()=plus_exprt(variable(arg0, 'i'), typecast_exprt(arg1, java_int_type()));
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
      results[0]=lshr_exprt(op[0], op[1]);
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
      results[0]=mod_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?cmp"))
    {
      assert(op.size()==2 && results.size()==1);

      // The integer result on the stack is:
      //  0 if op[0] equals op[1]
      // -1 if op[0] is less than op[1]
      //  1 if op[0] is greater than op[1]
      
      typet t=java_int_type();

      results[0]=
        if_exprt(binary_relation_exprt(op[0], ID_equal, op[1]), gen_zero(t),
        if_exprt(binary_relation_exprt(op[0], ID_gt, op[1]), from_integer(1, t),
        from_integer(-1, t)));
    }
    else if(statement==patternt("?cmpg"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=binary_relation_exprt(op[0], ID_gt, op[1]);
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
      results[0]=member_exprt(dereference_exprt(op[0]), arg0.get(ID_component_name));
    }
    else if(statement=="getstatic")
    {
      assert(op.empty() && results.size()==1);
      results[0]=arg0;
    }
    else if(statement=="putstatic")
    {
      assert(op.size()==1 && results.empty());
      c=code_assignt(arg0, op[0]);
    }
    else if(statement==patternt("?2?")) // i2c etc.
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_type(statement[2]));
    }
    else if(statement=="new")
    {
      // use temporary since the stack symbol might get duplicated
      assert(op.empty() && results.size()==1);
      reference_typet ref_type;
      ref_type.subtype()=arg0.type();
      exprt tmp=tmp_variable(ref_type);
      exprt new_expr=side_effect_exprt(ID_java_new, ref_type);
      new_expr.operands().resize(1);
      c=code_assignt(tmp, new_expr);
      results[0]=tmp;
    }
    else if(statement=="newarray")
    {
      assert(op.size()==1 && results.size()==1);

      const std::pair<typet, exprt> element_type(get_java_type(arg0.id()));
      struct_typet array_type;
      struct_typet::componentt length;
      length.set_name("length");
      length.type() = java_int_type();
      struct_typet::componentt data;
      data.set_name("data");
      data.type() = array_typet(element_type.first, op[0]);
      array_type.components().push_back(length);
      array_type.components().push_back(data);

      const pointer_typet ref_type(array_type);
      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.operands().resize(1);
      java_new_array.copy_to_operands(op[0]);
      const exprt tmp(tmp_variable(ref_type));
      c = code_assignt(tmp, java_new_array);
      results[0]=tmp;
    }
    else if(statement=="anewarray")
    {
      // use temporary since the stack symbol might get duplicated
      assert(op.size()==1 && results.size()==1);

      /*reference_typet ref_type(arg0.type());
      exprt tmp=tmp_variable(ref_type);
      exprt new_expr=side_effect_exprt(ID_java_new_array, ref_type);
      new_expr.operands().resize(2);
      new_expr.op1()=op[0]; // number of elements
      c=code_assignt(tmp, new_expr);
      results[0]=tmp;*/
      assert(!"TODO: Implement anewarray");
    }
    else if(statement=="arraylength")
    {
      assert(op.size() == 1 && results.size() == 1);
      const dereference_exprt array(op[0]);
      const member_exprt length(array, "length", java_int_type());
      results[0]=length;
    }
    else if(statement=="tableswitch")
    {
      assert(op.size()==1 && results.size()==1);
      c=codet(statement);
      c.copy_to_operands(op[0]);
    }
    else if(statement=="lookupswitch")
    {
      assert(op.size()==1 && results.size()==1);
      c=codet(statement);
      c.copy_to_operands(op[0]);
    }
    else
    {
      c=codet(statement);
      c.operands()=op;
    }

    push(results);

    {
      irep_idt l=label(i2string(i_it->address));

      if(targets.find(l)!=targets.end())
        code.add(code_labelt(l, c));
      else if(c.get_statement()!=ID_skip)
        code.add(c);
    }
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
    code_typet code_type=to_code_type(type); // copy
    
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
  const std::string &module,
  message_handlert &message_handler)
{
  java_bytecode_convertt java_bytecode_convert(symbol_table, message_handler);

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
