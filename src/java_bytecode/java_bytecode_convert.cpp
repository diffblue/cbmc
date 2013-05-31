/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <stack>

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/i2string.h>
#include <util/expr_util.h>

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
  inline patternt(const char *_p):p(_p)
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
  
  symbol_exprt variable(const irep_idt &id)
  {
    return symbol_exprt("java::local"+id2string(id), java_int_type());
  }
  
  irep_idt label(const irep_idt &address)
  {
    return "pc"+id2string(address);
  }

  void convert(const java_bytecode_parse_treet &parse_tree);
  void convert(const classt &c);
  void convert(symbolt &class_symbol, const membert &m);
  void convert(const instructiont &i);
  codet convert_instructions(const instructionst &);
  
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

  // Local Variables 
  typedef std::vector<exprt> varst;
  varst vars;
  
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
  
  // produce symbol
  symbolt new_symbol;
  new_symbol.base_name=c.name;
  new_symbol.name="java::"+id2string(c.name);
  new_symbol.type=class_type;
  
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

  if(m.method)
  {
    class_type.methods().push_back(class_typet::methodt());
    class_typet::methodt &method=class_type.methods().back();
    
    code_typet type;
    type.return_type()=m.type;
    //type.parameters()=m.parameters;
    
    method.set_base_name(m.name);
    method.set_name(m.name);
    method.type()=type;
    
    // create method symbol
    symbolt method_symbol;
    method_symbol.name=m.name;
    method_symbol.base_name=m.name;
    method_symbol.type=type;
    method_symbol.value=convert_instructions(m.instructions);
    symbol_table.add(method_symbol);
  }
  else
  {
    class_type.components().push_back(class_typet::componentt());
    class_typet::componentt &component=class_type.components().back();
    
    component.set_name(m.name);
    component.type()=m.type;
  }
}

/*******************************************************************\

Function: java_bytecode_convertt::convert_instructions

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

/*******************************************************************\

Function: java_bytecode_convertt::convert_instructions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

codet java_bytecode_convertt::convert_instructions(
  const instructionst &instructions)
{
  code_blockt code;

  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
  {
    codet c;
    c.make_nil();
  
    irep_idt statement=i_it->statement;
    irep_idt arg1=i_it->arg1;
    irep_idt arg2=i_it->arg2;
    
    const bytecode_infot &bytecode_info=get_bytecode_info(statement);
    
    // deal with _idx suffixes
    if(statement.size()>=2 &&
       statement[statement.size()-2]=='_' &&
       isdigit(statement[statement.size()-1]))
    {
      arg1=
        std::string(id2string(statement), statement.size()-1, 1);
      statement=std::string(id2string(statement), 0, statement.size()-2);
    }
    
    exprt::operandst op=pop(bytecode_info.pop);
    exprt::operandst results;
    results.resize(bytecode_info.push, nil_exprt());

    if(statement=="aconst_null")
    {
      assert(results.size()==1);
      results[0]=gen_zero(java_reference_type(typet()));
    }
    else if(statement=="athrow")
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=op[0];
    }
    else if(statement=="checkcast")
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=op[0];
    }
    else if(statement=="invokedynamic" ||
            statement=="invokeinterface" ||
            statement=="invokespecial" ||
            statement=="invokestatic" ||
            statement=="invokevirtual")
    {
      code_function_callt call;
      call.function()=symbol_exprt(arg1);
      c=call;
    }
    else if(statement=="return")
    {
      code_returnt code_return;
      c=code_return;
    }
    else if(statement==patternt("?return"))
    {
      assert(op.size()==1);
      code_returnt code_return(op[0]);
      c=code_return;
    }
    else if(statement==patternt("?astore"))
    {
      // store value into an array
      assert(op.size()==3 && results.empty());
      code_assignt code_assign;
      code_assign.lhs()=index_exprt(op[0], op[1]);
      code_assign.rhs()=op[2];
      c=code_assign;
    }
    else if(statement==patternt("?store"))
    {
      // store value into some local variable
      assert(op.size()==1 && results.empty());
      code_assignt code_assign;
      code_assign.lhs()=variable(arg1);
      code_assign.rhs()=op[0];
      c=code_assign;
    }
    else if(statement==patternt("?load"))
    {
      // load a value from a local variable
      results[0]=variable(arg1);
    }
    else if(statement=="goto")
    {
      code_gotot code_goto(label(arg1));
      c=code_goto;
    }
    else if(statement=="iconst_m1")
    {
      assert(results.size()==1);
      results[0]=from_integer(-1, java_int_type());
    }
    else if(statement=="iconst")
    {
      assert(results.size()==1);
      results[0]=from_integer(0, java_int_type());
    }
    else if(statement=="bipush")
    {
      assert(results.size()==1);
      mp_integer value=string2integer(id2string(arg1));
      results[0]=from_integer(value, java_int_type());
    }
    else if(statement==patternt("if_?cmp??"))
    {
      assert(op.size()==2 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_equal, op[1]);
      code_branch.then_case()=code_gotot(label(arg1));
      c=code_branch;
    }
    else if(statement==patternt("if??"))
    {
      assert(op.size()==2 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_equal, op[1]);
      code_branch.then_case()=code_gotot(label(arg1));
      c=code_branch;
    }
    else if(statement==patternt("ifnonnull"))
    {
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_notequal, gen_zero(java_int_type()));
      code_branch.then_case()=code_gotot(label(arg1));
      c=code_branch;
    }
    else if(statement==patternt("ifnull"))
    {
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_equal, gen_zero(java_int_type()));
      code_branch.then_case()=code_gotot(label(arg1));
      c=code_branch;
    }
    else if(statement=="iinc")
    {
      mp_integer value=string2integer(id2string(i_it->arg2));
      code_assignt code_assign;
      code_assign.lhs()=variable(arg1);
      code_assign.rhs()=
        plus_exprt(variable(arg1), from_integer(value, java_int_type()));
      c=code_assign;
    }
    else if(statement==patternt("?xor"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitxor_exprt(op[0], op[1]);
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
      results[0]=member_exprt(dereference_exprt(op[0]), arg1);
    }
    else if(statement=="getstatic")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement==patternt("?il"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_long_type());
    }
    else if(statement==patternt("?if"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_float_type());
    }
    else if(statement==patternt("?id"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_double_type());
    }
    else if(statement==patternt("?ib"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_byte_type());
    }
    else if(statement==patternt("?is"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_short_type());
    }
    else if(statement=="new")
    {
      assert(op.empty() && results.size()==1);
      symbol_typet obj_t(arg1);
      results[0]=side_effect_exprt(ID_cpp_new, obj_t);
    }
    else if(statement=="newarray")
    {
      assert(op.size()==1 && results.size()==1);
      symbol_typet obj_t(arg1);
      array_typet array_type(obj_t, op[0]);
      results[0]=side_effect_exprt(ID_cpp_new_array, array_type);
    }
    else if(statement=="anewarray")
    {
      assert(op.size()==1 && results.size()==1);
      symbol_typet obj_t(arg1);
      array_typet array_type(java_reference_type(obj_t), op[0]);
      results[0]=side_effect_exprt(ID_cpp_new_array, array_type);
    }
    else
      throw "unhandled statement "+id2string(statement);

    push(results);

    if(c.is_not_nil())
    {
      irep_idt a_str=i2string(i_it->address);
      code.add(code_labelt(label(a_str), c));
    }
  }
  
  return code;
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
  
  catch(int e)
  {    
  }

  catch(const char *e)
  {
    java_bytecode_convert.error(e);
  }

  catch(const std::string &e)
  {
    java_bytecode_convert.error(e);
  }

  return true;
}

