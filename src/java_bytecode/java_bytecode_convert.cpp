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
  
  irep_idt current_method;
  
  // JVM local variables
  struct vart
  {  
    symbol_exprt symbol_expr;
  };
  
  typedef std::map<irep_idt, vart> varst;
  varst vars;
  
  symbol_exprt read_variable(const exprt &arg)
  {
    irep_idt number=to_constant_expr(arg).get_value();
    return vars[number].symbol_expr;
  }
  
  symbol_exprt write_variable(const exprt &arg, const typet &type)
  {
    irep_idt number=to_constant_expr(arg).get_value();
    irep_idt identifier=id2string(current_method)+"::local"+id2string(number);
    vart &var=vars[number];
    var.symbol_expr=symbol_exprt(identifier, type);
    var.symbol_expr.set(ID_C_base_name, "local"+id2string(number));
    return var.symbol_expr;
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
  
  // produce symbol
  symbolt new_symbol;
  new_symbol.base_name=c.name;
  new_symbol.pretty_name=c.name;
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
    type.return_type()=convert(m.type);
    //type.parameters()=m.parameters;
    
    method.set_base_name(m.name);
    method.set_name(id2string(class_symbol.name)+"."+id2string(m.name));
    method.type()=type;
    
    // create method symbol
    symbolt method_symbol;
    method_symbol.name=method.get_name();
    method_symbol.base_name=method.get_base_name();
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                              id2string(method.get_base_name())+"()";
    method_symbol.type=type;
    current_method=method_symbol.name;
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
      code_assign.lhs()=write_variable(arg0, op[0].type());
      code_assign.rhs()=op[0];
      c=code_assign;
    }
    else if(statement==patternt("?load"))
    {
      // load a value from a local variable
      results[0]=read_variable(arg0);
    }
    else if(statement=="ldc" || statement=="ldc_w" ||
            statement=="ldc2" || statement=="ldc2_w")
    {
      assert(op.empty() && results.size()==1);
      results[0]=arg0;
    }
    else if(statement=="goto" || statement=="goto_w")
    {
      assert(op.empty() && results.size()==0);
      irep_idt number=to_constant_expr(arg0).get_value();
      code_gotot code_goto(label(number));
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
      results[0]=typecast_exprt(arg0, java_int_type());
    }
    else if(statement=="sipush")
    {
      assert(results.size()==1);
      results[0]=typecast_exprt(arg0, java_short_type());
    }
    else if(statement==patternt("if_?cmp??"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==2 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_equal, op[1]);
      code_branch.then_case()=code_gotot(label(number));
      c=code_branch;
    }
    else if(statement==patternt("if??"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], ID_equal, gen_zero(op[0].type()));
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
      code_assign.lhs()=write_variable(arg0, java_int_type());
      code_assign.rhs()=plus_exprt(read_variable(arg0), typecast_exprt(arg1, java_int_type()));
      c=code_assign;
    }
    else if(statement==patternt("?xor"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitxor_exprt(op[0], op[1]);
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
      results[0]=side_effect_exprt(ID_java_new, arg0.type());
    }
    else if(statement=="newarray")
    {
      assert(op.size()==1 && results.size()==1);
      array_typet array_type(arg0.type(), op[0]);
      results[0]=side_effect_exprt(ID_java_new_array, array_type);
    }
    else if(statement=="anewarray")
    {
      assert(op.size()==1 && results.size()==1);
      array_typet array_type(java_reference_type(arg0.type()), op[0]);
      results[0]=side_effect_exprt(ID_java_new_array, array_type);
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
