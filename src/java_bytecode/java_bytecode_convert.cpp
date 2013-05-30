/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_convert.h"

#if 0
aaload
aastore
aconst_null
aload
aload_0
aload_1
aload_2
aload_3
anewarray
areturn
arraylength
astore
astore_0
astore_1
astore_2
astore_3
athrow
baload
bastore
bipush
caload
castore
checkcast
dadd
daload
dastore
dcmpg
dcmpl
dconst_0
dconst_1
ddiv
dload
dload_0
dload_1
dload_2
dload_3
dmul
dneg
drem
dreturn
dstore
dstore_0
dstore_1
dstore_2
dstore_3
dsub
dup
dup_x1
dup_x2
dup2
dup2_x1
dup2_x2
fadd
faload
fastore
fcmpg
fcmpl
fconst_0
fconst_1
fconst_2
fdiv
fload
fload_0
fload_1
fload_2
fload_3
fmul
fneg
frem
freturn
fstore
fstore_0
fstore_1
fstore_2
fstore_3
fsub
getfield
getstatic
goto
goto_w
i2l
i2f
i2d
l2i
l2f
l2d
f2i
f2l
f2d
d2i
d2l
d2f
i2b
i2c
i2s
iadd
iaload
iand
iastore
iconst_m1
iconst_0
iconst_1
iconst_2
iconst_3
iconst_4
iconst_5
idiv
if_acmpeq
if_acmpne
if_icmpeq
if_icmpne
if_icmplt
if_icmpge
if_icmpgt
if_icmple
ifeq
ifne
iflt
ifge
ifgt
ifle
ifnonnull
ifnull
iinc
iload
iload_0
iload_1
iload_2
iload_3
imul
ineg
instanceof
invokedynamic
invokeinterface
invokespecial
invokestatic
invokevirtual
ior
irem
ireturn
ishl
ishr
istore
istore_0
istore_1
istore_2
istore_3
isub
iushr
ixor
jsr
jsr_w
ladd
laload
land
lastore
lcmp
lconst_0
lconst_1
ldc
ldc_w
ldc2_w
ldiv
lload
lload_0
lload_1
lload_2
lload_3
lmul
lneg
lookupswitch
lor
lrem
lreturn
lshl
lshr
lstore
lstore_0
lstore_1
lstore_2
lstore_3
lsub
lushr
lxor
monitorenter
monitorexit
multianewarray
new
newarray
nop
pop
pop2
putfield
putstatic
ret
return
saload
sastore
sipush
swap
tableswitch
wide
or
iinc, indexbyte1, indexbyte2, countbyte1, countbyte2
breakpoint
impdep1
impdep2
#endif

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

protected:
  symbol_tablet &symbol_table;

  void convert(const java_bytecode_parse_treet &parse_tree);
  void convert(const classt &c);
  void convert(const membert &m);
  void convert(const instructiont &i);
};

/*******************************************************************\

Function: java_bytecode_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convertt::convert(const java_bytecode_parse_treet &parse_tree)
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

  // produce symbol
  symbolt new_symbol;
  new_symbol.base_name=c.name;
  new_symbol.name="java::"+id2string(c.name);
  new_symbol.type=class_type;

  symbol_table.add(new_symbol);
}

/*******************************************************************\

Function: java_bytecode_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_convert(
  java_bytecode_parse_treet &parse_tree,
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

