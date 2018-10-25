/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_parser.h"

#include <algorithm>
#include <fstream>
#include <map>
#include <string>

#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/parser.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/optional.h>

#include "java_bytecode_parse_tree.h"
#include "java_types.h"
#include "bytecode_info.h"

#ifdef DEBUG
#include <iostream>
#endif

class java_bytecode_parsert:public parsert
{
public:
  java_bytecode_parsert()
  {
    get_bytecodes();
  }

  virtual bool parse();

  typedef java_bytecode_parse_treet::classt classt;
  typedef java_bytecode_parse_treet::classt::fieldst fieldst;
  typedef java_bytecode_parse_treet::classt::methodst methodst;
  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::fieldt fieldt;
  typedef java_bytecode_parse_treet::methodt::instructionst instructionst;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  typedef java_bytecode_parse_treet::annotationt annotationt;
  typedef java_bytecode_parse_treet::annotationst annotationst;
  typedef java_bytecode_parse_treet::classt::method_handle_typet
    method_handle_typet;
  typedef java_bytecode_parse_treet::classt::lambda_method_handlet
    lambda_method_handlet;
  typedef java_bytecode_parse_treet::classt::u2_valuest u2_valuest;

  java_bytecode_parse_treet parse_tree;

  struct pool_entryt
  {
    u1 tag;
    u2 ref1, ref2;
    irep_idt s;
    u8 number;
    exprt expr;
    pool_entryt():tag(0), ref1(0), ref2(0), number(0) { }
  };

  typedef std::vector<pool_entryt> constant_poolt;
  constant_poolt constant_pool;

protected:
  class bytecodet
  {
  public:
    irep_idt mnemonic;
    char format;
  };

  std::vector<bytecodet> bytecodes;

  pool_entryt &pool_entry(u2 index)
  {
    if(index==0 || index>=constant_pool.size())
    {
      error() << "invalid constant pool index (" << index << ")" << eom;
      error() << "constant pool size: " << constant_pool.size() << eom;
      throw 0;
    }

    return constant_pool[index];
  }

  exprt &constant(u2 index)
  {
    return pool_entry(index).expr;
  }

  const typet type_entry(u2 index)
  {
    return java_type_from_string(id2string(pool_entry(index).s));
  }

  void get_bytecodes()
  {
    // pre-hash the mnemonics, so we do this only once
    bytecodes.resize(256);
    for(const bytecode_infot *p=bytecode_info; p->mnemonic!=nullptr; p++)
    {
      assert(p->opcode<bytecodes.size());
      bytecodes[p->opcode].mnemonic=p->mnemonic;
      bytecodes[p->opcode].format=p->format;
    }
  }

  void rClassFile();
  void rconstant_pool();
  void rinterfaces(classt &parsed_class);
  void rfields(classt &parsed_class);
  void rmethods(classt &parsed_class);
  void rmethod(classt &parsed_class);
  void
  rinner_classes_attribute(classt &parsed_class, const u4 &attribute_length);
  std::vector<irep_idt> rexceptions_attribute();
  void rclass_attribute(classt &parsed_class);
  void rRuntimeAnnotation_attribute(annotationst &);
  void rRuntimeAnnotation(annotationt &);
  void relement_value_pairs(annotationt::element_value_pairst &);
  exprt get_relement_value();
  void rmethod_attribute(methodt &method);
  void rfield_attribute(fieldt &);
  void rcode_attribute(methodt &method);
  void read_verification_type_info(methodt::verification_type_infot &);
  void rbytecode(methodt::instructionst &);
  void get_class_refs();
  void get_class_refs_rec(const typet &);
  void parse_local_variable_type_table(methodt &method);
  optionalt<lambda_method_handlet>
  parse_method_handle(const class method_handle_infot &entry);
  void read_bootstrapmethods_entry(classt &);

  void skip_bytes(std::size_t bytes)
  {
    for(std::size_t i=0; i<bytes; i++)
    {
      if(!*in)
      {
        error() << "unexpected end of bytecode file" << eom;
        throw 0;
      }
      in->get();
    }
  }

  u8 read_bytes(size_t bytes)
  {
    u8 result=0;
    for(size_t i=0; i<bytes; i++)
    {
      if(!*in)
      {
        error() << "unexpected end of bytecode file" << eom;
        throw 0;
      }
      result<<=8;
      result|=in->get();
    }
    return result;
  }

  u1 read_u1()
  {
    return (u1)read_bytes(1);
  }

  inline u2 read_u2()
  {
    return (u2)read_bytes(2);
  }

  u4 read_u4()
  {
    return (u4)read_bytes(4);
  }

  u8 read_u8()
  {
    return read_bytes(8);
  }

  void store_unknown_method_handle(
    classt &parsed_class,
    size_t bootstrap_method_index,
    u2_valuest u2_values) const;
};

#define CONSTANT_Class                7
#define CONSTANT_Fieldref             9
#define CONSTANT_Methodref           10
#define CONSTANT_InterfaceMethodref  11
#define CONSTANT_String               8
#define CONSTANT_Integer              3
#define CONSTANT_Float                4
#define CONSTANT_Long                 5
#define CONSTANT_Double               6
#define CONSTANT_NameAndType         12
#define CONSTANT_Utf8                 1
#define CONSTANT_MethodHandle        15
#define CONSTANT_MethodType          16
#define CONSTANT_InvokeDynamic       18

#define VTYPE_INFO_TOP         0
#define VTYPE_INFO_INTEGER     1
#define VTYPE_INFO_FLOAT       2
#define VTYPE_INFO_LONG        3
#define VTYPE_INFO_DOUBLE      4
#define VTYPE_INFO_ITEM_NULL   5
#define VTYPE_INFO_UNINIT_THIS 6
#define VTYPE_INFO_OBJECT      7
#define VTYPE_INFO_UNINIT      8

class structured_pool_entryt
{
public:
  explicit structured_pool_entryt(java_bytecode_parsert::pool_entryt entry)
    : tag(entry.tag)
  {
  }

  u1 get_tag() const
  {
    return tag;
  }

  typedef std::function<java_bytecode_parsert::pool_entryt &(u2)>
    pool_entry_lookupt;
  typedef java_bytecode_parsert::pool_entryt pool_entryt;

protected:
  static std::string read_utf8_constant(const pool_entryt &entry)
  {
    INVARIANT(
      entry.tag == CONSTANT_Utf8, "Name entry must be a constant UTF-8");
    return id2string(entry.s);
  }

private:
  u1 tag;
};

/// Corresponds to the CONSTANT_Class_info Structure
/// Described in Java 8 specification 4.4.1
class class_infot : public structured_pool_entryt
{
public:
  explicit class_infot(const pool_entryt &entry) : structured_pool_entryt(entry)
  {
    PRECONDITION(entry.tag == CONSTANT_Class);
    name_index = entry.ref1;
  }

  std::string get_name(pool_entry_lookupt pool_entry) const
  {
    const pool_entryt &name_entry = pool_entry(name_index);
    return read_utf8_constant(name_entry);
  }

private:
  u2 name_index;
};

/// Corresponds to the CONSTANT_NameAndType_info Structure
/// Described in Java 8 specification 4.4.6
class name_and_type_infot : public structured_pool_entryt
{
public:
  explicit name_and_type_infot(java_bytecode_parsert::pool_entryt entry)
    : structured_pool_entryt(entry)
  {
    PRECONDITION(entry.tag == CONSTANT_NameAndType);
    name_index = entry.ref1;
    descriptor_index = entry.ref2;
  }

  std::string get_name(pool_entry_lookupt pool_entry) const
  {
    const pool_entryt &name_entry = pool_entry(name_index);
    return read_utf8_constant(name_entry);
  }

  std::string get_descriptor(pool_entry_lookupt pool_entry) const
  {
    const pool_entryt &descriptor_entry = pool_entry(descriptor_index);
    return read_utf8_constant(descriptor_entry);
  }

private:
  u2 name_index;
  u2 descriptor_index;
};

class base_ref_infot : public structured_pool_entryt
{
public:
  explicit base_ref_infot(pool_entryt entry) : structured_pool_entryt(entry)
  {
    PRECONDITION(
      entry.tag == CONSTANT_Fieldref || entry.tag == CONSTANT_Methodref ||
      entry.tag == CONSTANT_InterfaceMethodref);
    class_index = entry.ref1;
    name_and_type_index = entry.ref2;
  }

  u2 get_class_index() const
  {
    return class_index;
  }
  u2 get_name_and_type_index() const
  {
    return name_and_type_index;
  }

  name_and_type_infot get_name_and_type(pool_entry_lookupt pool_entry) const
  {
    const pool_entryt &name_and_type_entry = pool_entry(name_and_type_index);

    INVARIANT(
      name_and_type_entry.tag == CONSTANT_NameAndType,
      "name_and_typeindex did not correspond to a name_and_type in the "
      "constant pool");

    return name_and_type_infot{name_and_type_entry};
  }

  class_infot get_class(pool_entry_lookupt pool_entry) const
  {
    const pool_entryt &class_entry = pool_entry(class_index);

    return class_infot{class_entry};
  }

private:
  u2 class_index;
  u2 name_and_type_index;
};

class method_handle_infot : public structured_pool_entryt
{
public:
  /// Correspond to the different valid values for field reference_kind From
  /// Java 8 spec 4.4.8
  /// (https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html)
  enum class method_handle_kindt
  {
    REF_getField = 1,
    REF_getStatic = 2,
    REF_putField = 3,
    REF_putStatic = 4,
    REF_invokeVirtual = 5,
    REF_invokeStatic = 6,
    REF_invokeSpecial = 7,
    REF_newInvokeSpecial = 8,
    REF_invokeInterface = 9
  };

  explicit method_handle_infot(java_bytecode_parsert::pool_entryt entry)
    : structured_pool_entryt(entry)
  {
    PRECONDITION(entry.tag == CONSTANT_MethodHandle);
    PRECONDITION(entry.ref1 > 0 && entry.ref1 < 10); // Java 8 spec 4.4.8
    reference_kind = static_cast<method_handle_kindt>(entry.ref1);
    reference_index = entry.ref2;
  }

  base_ref_infot get_reference(pool_entry_lookupt pool_entry) const
  {
    const base_ref_infot ref_entry{pool_entry(reference_index)};

    // validate the correctness of the constant pool entry
    switch(reference_kind)
    {
    case method_handle_kindt::REF_getField:
    case method_handle_kindt::REF_getStatic:
    case method_handle_kindt::REF_putField:
    case method_handle_kindt::REF_putStatic:
    {
      INVARIANT(ref_entry.get_tag() == CONSTANT_Fieldref, "4.4.2");
      break;
    }
    case method_handle_kindt::REF_invokeVirtual:
    case method_handle_kindt::REF_newInvokeSpecial:
    {
      INVARIANT(ref_entry.get_tag() == CONSTANT_Methodref, "4.4.2");
      break;
    }
    case method_handle_kindt::REF_invokeStatic:
    case method_handle_kindt::REF_invokeSpecial:
    {
      INVARIANT(
        ref_entry.get_tag() == CONSTANT_Methodref ||
          ref_entry.get_tag() == CONSTANT_InterfaceMethodref,
        "4.4.2");
      break;
    }
    case method_handle_kindt::REF_invokeInterface:
    {
      INVARIANT(ref_entry.get_tag() == CONSTANT_InterfaceMethodref, "");
      break;
    }
    }

    return ref_entry;
  }

private:
  method_handle_kindt reference_kind;
  u2 reference_index;
};

bool java_bytecode_parsert::parse()
{
  try
  {
    rClassFile();
  }

  catch(const char *message)
  {
    error() << message << eom;
    return true;
  }

  catch(const std::string &message)
  {
    error() << message << eom;
    return true;
  }

  catch(...)
  {
    error() << "parsing error" << eom;
    return true;
  }

  return false;
}

#define ACC_PUBLIC       0x0001
#define ACC_PRIVATE      0x0002
#define ACC_PROTECTED    0x0004
#define ACC_STATIC       0x0008
#define ACC_FINAL        0x0010
#define ACC_SYNCHRONIZED 0x0020
#define ACC_BRIDGE       0x0040
#define ACC_NATIVE       0x0100
#define ACC_INTERFACE    0x0200
#define ACC_ABSTRACT     0x0400
#define ACC_STRICT       0x0800
#define ACC_SYNTHETIC    0x1000
#define ACC_ANNOTATION   0x2000
#define ACC_ENUM         0x4000

#define UNUSED_u2(x) { const u2 x = read_u2(); (void)x; } (void)0

void java_bytecode_parsert::rClassFile()
{
  parse_tree.loading_successful=false;

  u4 magic=read_u4();
  UNUSED_u2(minor_version);
  u2 major_version=read_u2();

  if(magic!=0xCAFEBABE)
  {
    error() << "wrong magic" << eom;
    throw 0;
  }

  if(major_version<44)
  {
    error() << "unexpected major version" << eom;
    throw 0;
  }

  rconstant_pool();

  classt &parsed_class=parse_tree.parsed_class;

  u2 access_flags=read_u2();
  u2 this_class=read_u2();
  u2 super_class=read_u2();

  parsed_class.is_abstract=(access_flags&ACC_ABSTRACT)!=0;
  parsed_class.is_enum=(access_flags&ACC_ENUM)!=0;
  parsed_class.is_public=(access_flags&ACC_PUBLIC)!=0;
  parsed_class.is_protected=(access_flags&ACC_PROTECTED)!=0;
  parsed_class.is_private=(access_flags&ACC_PRIVATE)!=0;
  parsed_class.is_final = (access_flags & ACC_FINAL) != 0;
  parsed_class.is_interface = (access_flags & ACC_INTERFACE) != 0;
  parsed_class.is_synthetic = (access_flags & ACC_SYNTHETIC) != 0;
  parsed_class.is_annotation = (access_flags & ACC_ANNOTATION) != 0;
  parsed_class.name=
    constant(this_class).type().get(ID_C_base_name);

  if(super_class!=0)
    parsed_class.super_class = constant(super_class).type().get(ID_C_base_name);

  rinterfaces(parsed_class);
  rfields(parsed_class);
  rmethods(parsed_class);

  // count elements of enum
  if(parsed_class.is_enum)
    for(fieldt &field : parse_tree.parsed_class.fields)
      if(field.is_enum)
        parse_tree.parsed_class.enum_elements++;

  u2 attributes_count=read_u2();

  for(std::size_t j=0; j<attributes_count; j++)
    rclass_attribute(parsed_class);

  get_class_refs();

  parse_tree.loading_successful=true;
}

/// Get the class references for the benefit of a dependency analysis.
void java_bytecode_parsert::get_class_refs()
{
  for(const auto &c : constant_pool)
  {
    switch(c.tag)
    {
    case CONSTANT_Class:
      get_class_refs_rec(c.expr.type());
      break;

    case CONSTANT_NameAndType:
      {
        typet t=java_type_from_string(id2string(pool_entry(c.ref2).s));
        get_class_refs_rec(t);
      }
      break;

    default: {}
    }
  }

  for(const auto &field : parse_tree.parsed_class.fields)
  {
    typet field_type;
    if(field.signature.has_value())
    {
      field_type=java_type_from_string_with_exception(
        field.descriptor,
        field.signature,
        "java::"+id2string(parse_tree.parsed_class.name));

      // add generic type args to class refs as dependencies, same below for
      // method types and entries from the local variable type table
      get_dependencies_from_generic_parameters(
        field_type, parse_tree.class_refs);
    }
    else
      field_type=java_type_from_string(field.descriptor);

    get_class_refs_rec(field_type);
  }

  for(const auto &method : parse_tree.parsed_class.methods)
  {
    typet method_type;
    if(method.signature.has_value())
    {
      method_type=java_type_from_string_with_exception(
        method.descriptor,
        method.signature,
        "java::"+id2string(parse_tree.parsed_class.name));
      get_dependencies_from_generic_parameters(
        method_type, parse_tree.class_refs);
    }
    else
      method_type=java_type_from_string(method.descriptor);

    get_class_refs_rec(method_type);
    for(const auto &var : method.local_variable_table)
    {
      typet var_type;
      if(var.signature.has_value())
      {
        var_type=java_type_from_string_with_exception(
          var.descriptor,
          var.signature,
          "java::"+id2string(parse_tree.parsed_class.name));
        get_dependencies_from_generic_parameters(
          var_type, parse_tree.class_refs);
      }
      else
        var_type=java_type_from_string(var.descriptor);
      get_class_refs_rec(var_type);
    }
  }
}

void java_bytecode_parsert::get_class_refs_rec(const typet &src)
{
  if(src.id()==ID_code)
  {
    const java_method_typet &ct = to_java_method_type(src);
    const typet &rt=ct.return_type();
    get_class_refs_rec(rt);
    for(const auto &p : ct.parameters())
      get_class_refs_rec(p.type());
  }
  else if(src.id()==ID_symbol_type)
  {
    irep_idt name=src.get(ID_C_base_name);
    if(has_prefix(id2string(name), "array["))
    {
      const typet &element_type =
        static_cast<const typet &>(src.find(ID_element_type));
      get_class_refs_rec(element_type);
    }
    else
      parse_tree.class_refs.insert(name);
  }
  else if(src.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(src);
    for(const auto &c : struct_type.components())
      get_class_refs_rec(c.type());
  }
  else if(src.id()==ID_pointer)
    get_class_refs_rec(src.subtype());
}

void java_bytecode_parsert::rconstant_pool()
{
  u2 constant_pool_count=read_u2();
  if(constant_pool_count==0)
  {
    error() << "invalid constant_pool_count" << eom;
    throw 0;
  }

  constant_pool.resize(constant_pool_count);

  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    // the first entry isn't used
    if(it==constant_pool.begin())
      continue;

    it->tag=read_u1();

    switch(it->tag)
    {
    case CONSTANT_Class:
      it->ref1=read_u2();
      break;

    case CONSTANT_Fieldref:
    case CONSTANT_Methodref:
    case CONSTANT_InterfaceMethodref:
    case CONSTANT_NameAndType:
    case CONSTANT_InvokeDynamic:
      it->ref1=read_u2();
      it->ref2=read_u2();
      break;

    case CONSTANT_String:
    case CONSTANT_MethodType:
      it->ref1=read_u2();
      break;

    case CONSTANT_Integer:
    case CONSTANT_Float:
      it->number=read_u4();
      break;

    case CONSTANT_Long:
    case CONSTANT_Double:
      it->number=read_u8();
      // Eight-byte constants take up two entries
      // in the constant_pool table, for annoying this programmer.
      if(it==constant_pool.end())
      {
        error() << "invalid double entry" << eom;
        throw 0;
      }
      it++;
      it->tag=0;
      break;

    case CONSTANT_Utf8:
      {
        u2 bytes=read_u2();
        std::string s;
        s.resize(bytes);
        for(std::string::iterator s_it=s.begin(); s_it!=s.end(); s_it++)
          *s_it=read_u1();
        it->s=s; // hashes
      }
      break;

    case CONSTANT_MethodHandle:
      it->ref1=read_u1();
      it->ref2=read_u2();
      break;

    default:
      error() << "unknown constant pool entry (" << it->tag << ")"
              << eom;
      throw 0;
    }
  }

  // we do a bit of post-processing after we have them all
  for(constant_poolt::iterator
      it=constant_pool.begin();
      it!=constant_pool.end();
      it++)
  {
    // the first entry isn't used
    if(it==constant_pool.begin())
      continue;

    switch(it->tag)
    {
    case CONSTANT_Class:
      {
        const std::string &s=id2string(pool_entry(it->ref1).s);
        it->expr=type_exprt(java_classname(s));
      }
      break;

    case CONSTANT_Fieldref:
      {
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        const pool_entryt &name_entry=pool_entry(nameandtype_entry.ref1);
        const pool_entryt &class_entry=pool_entry(it->ref1);
        const pool_entryt &class_name_entry=pool_entry(class_entry.ref1);
        typet type=type_entry(nameandtype_entry.ref2);

        symbol_typet class_symbol=
          java_classname(id2string(class_name_entry.s));

        fieldref_exprt fieldref(
          type, name_entry.s, class_symbol.get_identifier());

        it->expr=fieldref;
      }
      break;

    case CONSTANT_Methodref:
    case CONSTANT_InterfaceMethodref:
      {
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        const pool_entryt &name_entry=pool_entry(nameandtype_entry.ref1);
        const pool_entryt &class_entry=pool_entry(it->ref1);
        const pool_entryt &class_name_entry=pool_entry(class_entry.ref1);
        typet type=type_entry(nameandtype_entry.ref2);

        symbol_typet class_symbol=
          java_classname(id2string(class_name_entry.s));

        irep_idt component_name=
          id2string(name_entry.s)+
          ":"+id2string(pool_entry(nameandtype_entry.ref2).s);

        irep_idt class_name=
          class_symbol.get_identifier();

        irep_idt identifier=
          id2string(class_name)+"."+id2string(component_name);

        exprt virtual_function(ID_virtual_function, type);
        virtual_function.set(ID_component_name, component_name);
        virtual_function.set(ID_C_class, class_name);
        virtual_function.set(ID_C_base_name, name_entry.s);
        virtual_function.set(ID_identifier, identifier);

        it->expr=virtual_function;
      }
      break;

    case CONSTANT_String:
      {
        // ldc turns these into references to java.lang.String
        exprt string_literal(ID_java_string_literal);
        string_literal.set(ID_value, pool_entry(it->ref1).s);
        it->expr=string_literal;
      }
      break;

    case CONSTANT_Integer:
      it->expr=from_integer(it->number, java_int_type());
      break;

    case CONSTANT_Float:
      {
        ieee_floatt value(ieee_float_spect::single_precision());
        value.unpack(it->number);
        it->expr=value.to_expr();
      }
      break;

    case CONSTANT_Long:
      it->expr=from_integer(it->number, java_long_type());
      break;

    case CONSTANT_Double:
      {
        ieee_floatt value(ieee_float_spect::double_precision());
        value.unpack(it->number);
        it->expr=value.to_expr();
      }
      break;

    case CONSTANT_NameAndType:
      {
        it->expr.id("nameandtype");
      }
      break;

    case CONSTANT_MethodHandle:
      {
        it->expr.id("methodhandle");
      }
      break;

    case CONSTANT_MethodType:
      {
        it->expr.id("methodtype");
      }
      break;

    case CONSTANT_InvokeDynamic:
      {
        it->expr.id("invokedynamic");
        const pool_entryt &nameandtype_entry=pool_entry(it->ref2);
        typet type=type_entry(nameandtype_entry.ref2);
        type.set(ID_java_lambda_method_handle_index, it->ref1);
        it->expr.type()=type;
      }
      break;

    default:{};
    }
  }
}

void java_bytecode_parsert::rinterfaces(classt &parsed_class)
{
  u2 interfaces_count=read_u2();

  for(std::size_t i=0; i<interfaces_count; i++)
    parsed_class.implements
      .push_back(constant(read_u2()).type().get(ID_C_base_name));
}

void java_bytecode_parsert::rfields(classt &parsed_class)
{
  u2 fields_count=read_u2();

  for(std::size_t i=0; i<fields_count; i++)
  {
    fieldt &field=parsed_class.add_field();

    u2 access_flags=read_u2();
    u2 name_index=read_u2();
    u2 descriptor_index=read_u2();
    u2 attributes_count=read_u2();

    field.name=pool_entry(name_index).s;
    field.is_static=(access_flags&ACC_STATIC)!=0;
    field.is_final=(access_flags&ACC_FINAL)!=0;
    field.is_enum=(access_flags&ACC_ENUM)!=0;

    field.descriptor=id2string(pool_entry(descriptor_index).s);
    field.is_public=(access_flags&ACC_PUBLIC)!=0;
    field.is_protected=(access_flags&ACC_PROTECTED)!=0;
    field.is_private=(access_flags&ACC_PRIVATE)!=0;
    const auto flags = (field.is_public ? 1 : 0) +
      (field.is_protected?1:0)+
      (field.is_private?1:0);
    DATA_INVARIANT(flags<=1, "at most one of public, protected, private");

    for(std::size_t j=0; j<attributes_count; j++)
      rfield_attribute(field);
  }
}

#define T_BOOLEAN 4
#define T_CHAR    5
#define T_FLOAT   6
#define T_DOUBLE  7
#define T_BYTE    8
#define T_SHORT   9
#define T_INT    10
#define T_LONG   11

void java_bytecode_parsert::rbytecode(
  methodt::instructionst &instructions)
{
  u4 code_length=read_u4();

  u4 address;
  size_t bytecode_index=0; // index of bytecode instruction

  for(address=0; address<code_length; address++)
  {
    bool wide_instruction=false;
    u4 start_of_instruction=address;

    u1 bytecode=read_u1();

    if(bytecode==0xc4) // wide
    {
      wide_instruction=true;
      address++;
      bytecode=read_u1();
      // The only valid instructions following a wide byte are
      // [ifald]load, [ifald]store, ret and iinc
      // All of these have either format of v, or V
      INVARIANT(
        bytecodes[bytecode].format == 'v' || bytecodes[bytecode].format == 'V',
        "Unexpected wide instruction: " +
          id2string(bytecodes[bytecode].mnemonic));
    }

    instructions.push_back(instructiont());
    instructiont &instruction=instructions.back();
    instruction.statement=bytecodes[bytecode].mnemonic;
    instruction.address=start_of_instruction;
    instruction.source_location
      .set_java_bytecode_index(std::to_string(bytecode_index));

    switch(bytecodes[bytecode].format)
    {
    case ' ': // no further bytes
      break;

    case 'c': // a constant_pool index (one byte)
      if(wide_instruction)
      {
        instruction.args.push_back(constant(read_u2()));
        address+=2;
      }
      else
      {
        instruction.args.push_back(constant(read_u1()));
        address+=1;
      }
      break;

    case 'C': // a constant_pool index (two bytes)
      instruction.args.push_back(constant(read_u2()));
      address+=2;
      break;

    case 'b': // a signed byte
      {
        s1 c=read_u1();
        instruction.args.push_back(from_integer(c, signedbv_typet(8)));
      }
      address+=1;
      break;

    case 'o': // two byte branch offset, signed
      {
        s2 offset=read_u2();
        // By converting the signed offset into an absolute address (by adding
        // the current address) the number represented becomes unsigned.
        instruction.args.push_back(
          from_integer(address+offset, unsignedbv_typet(16)));
      }
      address+=2;
      break;

    case 'O': // four byte branch offset, signed
      {
        s4 offset=read_u4();
        // By converting the signed offset into an absolute address (by adding
        // the current address) the number represented becomes unsigned.
        instruction.args.push_back(
          from_integer(address+offset, unsignedbv_typet(32)));
      }
      address+=4;
      break;

    case 'v': // local variable index (one byte)
      {
        if(wide_instruction)
        {
          u2 v = read_u2();
          instruction.args.push_back(from_integer(v, unsignedbv_typet(16)));
          address += 2;
        }
        else
        {
          u1 v = read_u1();
          instruction.args.push_back(from_integer(v, unsignedbv_typet(8)));
          address += 1;
        }
      }

      break;

    case 'V':
      // local variable index (two bytes) plus two signed bytes
      if(wide_instruction)
      {
        u2 v=read_u2();
        instruction.args.push_back(from_integer(v, unsignedbv_typet(16)));
        s2 c=read_u2();
        instruction.args.push_back(from_integer(c, signedbv_typet(16)));
        address+=4;
      }
      else // local variable index (one byte) plus one signed byte
      {
        u1 v=read_u1();
        instruction.args.push_back(from_integer(v, unsignedbv_typet(8)));
        s1 c=read_u1();
        instruction.args.push_back(from_integer(c, signedbv_typet(8)));
        address+=2;
      }
      break;

    case 'I': // two byte constant_pool index plus two bytes
      {
        u2 c=read_u2();
        instruction.args.push_back(constant(c));
        u1 b1=read_u1();
        instruction.args.push_back(from_integer(b1, unsignedbv_typet(8)));
        u1 b2=read_u1();
        instruction.args.push_back(from_integer(b2, unsignedbv_typet(8)));
      }
      address+=4;
      break;

    case 'L': // lookupswitch
      {
        u4 base_offset=address;

        // first a pad to 32-bit align
        while(((address+1)&3)!=0) { read_u1(); address++; }

        // now default value
        s4 default_value=read_u4();
        // By converting the signed offset into an absolute address (by adding
        // the current address) the number represented becomes unsigned.
        instruction.args.push_back(
          from_integer(base_offset+default_value, unsignedbv_typet(32)));
        address+=4;

        // number of pairs
        u4 npairs=read_u4();
        address+=4;

        for(std::size_t i=0; i<npairs; i++)
        {
          s4 match=read_u4();
          s4 offset=read_u4();
          instruction.args.push_back(
            from_integer(match, signedbv_typet(32)));
          // By converting the signed offset into an absolute address (by adding
          // the current address) the number represented becomes unsigned.
          instruction.args.push_back(
            from_integer(base_offset+offset, unsignedbv_typet(32)));
          address+=8;
        }
      }
      break;

    case 'T': // tableswitch
      {
        size_t base_offset=address;

        // first a pad to 32-bit align
        while(((address+1)&3)!=0) { read_u1(); address++; }

        // now default value
        s4 default_value=read_u4();
        instruction.args.push_back(
          from_integer(base_offset+default_value, signedbv_typet(32)));
        address+=4;

        // now low value
        s4 low_value=read_u4();
        address+=4;

        // now high value
        s4 high_value=read_u4();
        address+=4;

        // there are high-low+1 offsets, and they are signed
        for(s4 i=low_value; i<=high_value; i++)
        {
          s4 offset=read_u4();
          instruction.args.push_back(from_integer(i, signedbv_typet(32)));
          // By converting the signed offset into an absolute address (by adding
          // the current address) the number represented becomes unsigned.
          instruction.args.push_back(
            from_integer(base_offset+offset, unsignedbv_typet(32)));
          address+=4;
        }
      }
      break;

    case 'm': // multianewarray: constant-pool index plus one unsigned byte
      {
        u2 c=read_u2(); // constant-pool index
        instruction.args.push_back(constant(c));
        u1 dimensions=read_u1(); // number of dimensions
        instruction.args.push_back(
          from_integer(dimensions, unsignedbv_typet(8)));
        address+=3;
      }
      break;

    case 't': // array subtype, one byte
      {
        typet t;
        switch(read_u1())
        {
        case T_BOOLEAN: t.id(ID_bool); break;
        case T_CHAR: t.id(ID_char); break;
        case T_FLOAT: t.id(ID_float); break;
        case T_DOUBLE: t.id(ID_double); break;
        case T_BYTE: t.id(ID_byte); break;
        case T_SHORT: t.id(ID_short); break;
        case T_INT: t.id(ID_int); break;
        case T_LONG: t.id(ID_long); break;
        default:{};
        }
        instruction.args.push_back(type_exprt(t));
      }
      address+=1;
      break;

    case 's': // a signed short
      {
        s2 s=read_u2();
        instruction.args.push_back(from_integer(s, signedbv_typet(16)));
      }
      address+=2;
      break;

    default:
      throw "unknown JVM bytecode instruction";
    }
    bytecode_index++;
  }

  if(address!=code_length)
  {
    error() << "bytecode length mismatch" << eom;
    throw 0;
  }
}

void java_bytecode_parsert::rmethod_attribute(methodt &method)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="Code")
  {
    UNUSED_u2(max_stack);
    UNUSED_u2(max_locals);

    rbytecode(method.instructions);

    u2 exception_table_length=read_u2();
    method.exception_table.resize(exception_table_length);

    for(std::size_t e=0; e<exception_table_length; e++)
    {
      u2 start_pc=read_u2();
      u2 end_pc=read_u2();

      // from the class file format spec ("4.7.3. The Code Attribute" for Java8)
      INVARIANT(
        start_pc < end_pc,
        "The start_pc must be less than the end_pc as this is the range the "
        "exception is active");

      u2 handler_pc=read_u2();
      u2 catch_type=read_u2();
      method.exception_table[e].start_pc=start_pc;
      method.exception_table[e].end_pc=end_pc;
      method.exception_table[e].handler_pc=handler_pc;
      if(catch_type!=0)
        method.exception_table[e].catch_type=
          to_symbol_type(pool_entry(catch_type).expr.type());
    }

    u2 attributes_count=read_u2();

    for(std::size_t j=0; j<attributes_count; j++)
      rcode_attribute(method);

    irep_idt line_number;

    // add missing line numbers
    for(methodt::instructionst::iterator
        it=method.instructions.begin();
        it!=method.instructions.end();
        it++)
    {
      if(!it->source_location.get_line().empty())
        line_number=it->source_location.get_line();
      else if(!line_number.empty())
        it->source_location.set_line(line_number);
      it->source_location
        .set_function(
          "java::"+id2string(parse_tree.parsed_class.name)+"."+
          id2string(method.name)+":"+method.descriptor);
    }

    // line number of method
    if(!method.instructions.empty())
      method.source_location.set_line(
        method.instructions.begin()->source_location.get_line());
  }
  else if(attribute_name=="Signature")
  {
    u2 signature_index=read_u2();
    method.signature=id2string(pool_entry(signature_index).s);
  }
  else if(attribute_name=="RuntimeInvisibleAnnotations" ||
          attribute_name=="RuntimeVisibleAnnotations")
  {
    rRuntimeAnnotation_attribute(method.annotations);
  }
  else if(
    attribute_name == "RuntimeInvisibleParameterAnnotations" ||
    attribute_name == "RuntimeVisibleParameterAnnotations")
  {
    u1 parameter_count = read_u1();
    // There may be attributes for both runtime-visiible and rutime-invisible
    // annotations, the length of either array may be longer than the other as
    // trailing parameters without annotations are omitted.
    // Extend our parameter_annotations if this one is longer than the one
    // previously recorded (if any).
    if(method.parameter_annotations.size() < parameter_count)
      method.parameter_annotations.resize(parameter_count);
    for(u2 param_no = 0; param_no < parameter_count; ++param_no)
      rRuntimeAnnotation_attribute(method.parameter_annotations[param_no]);
  }
  else if(attribute_name == "Exceptions")
  {
    method.throws_exception_table = rexceptions_attribute();
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::rfield_attribute(fieldt &field)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="Signature")
  {
    u2 signature_index=read_u2();
    field.signature=id2string(pool_entry(signature_index).s);
  }
  else if(attribute_name=="RuntimeInvisibleAnnotations" ||
     attribute_name=="RuntimeVisibleAnnotations")
  {
    rRuntimeAnnotation_attribute(field.annotations);
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::rcode_attribute(methodt &method)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="LineNumberTable")
  {
    // address -> instructiont
    typedef std::map<unsigned,
                     methodt::instructionst::iterator> instruction_mapt;
    instruction_mapt instruction_map;

    for(methodt::instructionst::iterator
        it=method.instructions.begin();
        it!=method.instructions.end();
        it++)
    {
      instruction_map[it->address]=it;
    }

    u2 line_number_table_length=read_u2();

    for(std::size_t i=0; i<line_number_table_length; i++)
    {
      u2 start_pc=read_u2();
      u2 line_number=read_u2();

      // annotate the bytecode program
      instruction_mapt::const_iterator it=
        instruction_map.find(start_pc);

      if(it!=instruction_map.end())
        it->second->source_location.set_line(line_number);
    }
  }
  else if(attribute_name=="LocalVariableTable")
  {
    u2 local_variable_table_length=read_u2();

    method.local_variable_table.resize(local_variable_table_length);

    for(std::size_t i=0; i<local_variable_table_length; i++)
    {
      u2 start_pc=read_u2();
      u2 length=read_u2();
      u2 name_index=read_u2();
      u2 descriptor_index=read_u2();
      u2 index=read_u2();

      method.local_variable_table[i].index=index;
      method.local_variable_table[i].name=pool_entry(name_index).s;
      method.local_variable_table[i].descriptor=
        id2string(pool_entry(descriptor_index).s);
      method.local_variable_table[i].start_pc=start_pc;
      method.local_variable_table[i].length=length;
    }
  }
  else if(attribute_name=="LocalVariableTypeTable")
  {
    parse_local_variable_type_table(method);
  }
  else if(attribute_name=="StackMapTable")
  {
    u2 stack_map_entries=read_u2();

    method.stack_map_table.resize(stack_map_entries);

    for(size_t i=0; i<stack_map_entries; i++)
    {
      u1 frame_type=read_u1();
      if(frame_type<=63)
      {
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::SAME;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(0);
      }
      else if(64<=frame_type && frame_type<=127)
      {
        method.stack_map_table[i].type=
          methodt::stack_map_table_entryt::SAME_LOCALS_ONE_STACK;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(1);
        methodt::verification_type_infot verification_type_info;
        read_verification_type_info(verification_type_info);
        method.stack_map_table[i].stack[0]=verification_type_info;
      }
      else if(frame_type==247)
      {
        method.stack_map_table[i].type=
          methodt::stack_map_table_entryt::SAME_LOCALS_ONE_STACK_EXTENDED;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(1);
        methodt::verification_type_infot verification_type_info;
        u2 offset_delta=read_u2();
        read_verification_type_info(verification_type_info);
        method.stack_map_table[i].stack[0]=verification_type_info;
        method.stack_map_table[i].offset_delta=offset_delta;
      }
      else if(248<=frame_type && frame_type<=250)
      {
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::CHOP;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(0);
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
      }
      else if(frame_type==251)
      {
        method.stack_map_table[i].type
          =methodt::stack_map_table_entryt::SAME_EXTENDED;
        method.stack_map_table[i].locals.resize(0);
        method.stack_map_table[i].stack.resize(0);
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
      }
      else if(252<=frame_type && frame_type<=254)
      {
        size_t new_locals=(size_t) (frame_type-251);
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::APPEND;
        method.stack_map_table[i].locals.resize(new_locals);
        method.stack_map_table[i].stack.resize(0);
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
        for(size_t k=0; k<new_locals; k++)
        {
          method.stack_map_table[i].locals
            .push_back(methodt::verification_type_infot());
          methodt::verification_type_infot &v=
            method.stack_map_table[i].locals.back();
          read_verification_type_info(v);
        }
      }
      else if(frame_type==255)
      {
        method.stack_map_table[i].type=methodt::stack_map_table_entryt::FULL;
        u2 offset_delta=read_u2();
        method.stack_map_table[i].offset_delta=offset_delta;
        u2 number_locals=read_u2();
        method.stack_map_table[i].locals.resize(number_locals);
        for(size_t k=0; k<(size_t) number_locals; k++)
        {
          method.stack_map_table[i].locals
            .push_back(methodt::verification_type_infot());
          methodt::verification_type_infot &v=
            method.stack_map_table[i].locals.back();
          read_verification_type_info(v);
        }
        u2 number_stack_items=read_u2();
        method.stack_map_table[i].stack.resize(number_stack_items);
        for(size_t k=0; k<(size_t) number_stack_items; k++)
        {
          method.stack_map_table[i].stack
            .push_back(methodt::verification_type_infot());
          methodt::verification_type_infot &v=
            method.stack_map_table[i].stack.back();
          read_verification_type_info(v);
        }
      }
      else
        throw "error: unknown stack frame type encountered";
    }
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::read_verification_type_info(
  methodt::verification_type_infot &v)
{
  u1 tag=read_u1();
  switch(tag)
  {
  case VTYPE_INFO_TOP:
    v.type=methodt::verification_type_infot::TOP;
    break;
  case VTYPE_INFO_INTEGER:
    v.type=methodt::verification_type_infot::INTEGER;
    break;
  case VTYPE_INFO_FLOAT:
    v.type=methodt::verification_type_infot::FLOAT;
    break;
  case VTYPE_INFO_LONG:
    v.type=methodt::verification_type_infot::LONG;
    break;
  case VTYPE_INFO_DOUBLE:
    v.type=methodt::verification_type_infot::DOUBLE;
    break;
  case VTYPE_INFO_ITEM_NULL:
    v.type=methodt::verification_type_infot::ITEM_NULL;
    break;
  case VTYPE_INFO_UNINIT_THIS:
    v.type=methodt::verification_type_infot::UNINITIALIZED_THIS;
    break;
  case VTYPE_INFO_OBJECT:
    v.type=methodt::verification_type_infot::OBJECT;
    v.cpool_index=read_u2();
    break;
  case VTYPE_INFO_UNINIT:
    v.type=methodt::verification_type_infot::UNINITIALIZED;
    v.offset=read_u2();
    break;
  default:
    throw "error: unknown verification type info encountered";
  }
}

void java_bytecode_parsert::rRuntimeAnnotation_attribute(
  annotationst &annotations)
{
  u2 num_annotations=read_u2();

  for(u2 number=0; number<num_annotations; number++)
  {
    annotationt annotation;
    rRuntimeAnnotation(annotation);
    annotations.push_back(annotation);
  }
}

void java_bytecode_parsert::rRuntimeAnnotation(
  annotationt &annotation)
{
  u2 type_index=read_u2();
  annotation.type=type_entry(type_index);
  relement_value_pairs(annotation.element_value_pairs);
}

void java_bytecode_parsert::relement_value_pairs(
  annotationt::element_value_pairst &element_value_pairs)
{
  u2 num_element_value_pairs=read_u2();
  element_value_pairs.resize(num_element_value_pairs);

  for(auto &element_value_pair : element_value_pairs)
  {
    u2 element_name_index=read_u2();
    element_value_pair.element_name=pool_entry(element_name_index).s;
    element_value_pair.value = get_relement_value();
  }
}

/// Corresponds to the element_value structure
/// Described in Java 8 specification 4.7.16.1
/// https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.7.16.1
/// \returns An exprt that represents the particular value of annotations field.
///   This is usually one of: a byte, number of some sort, string, character,
///   enum, Class type, array or another annotation.
exprt java_bytecode_parsert::get_relement_value()
{
  u1 tag=read_u1();

  switch(tag)
  {
  case 'e':
    {
      UNUSED_u2(type_name_index);
      UNUSED_u2(const_name_index);
      // todo: enum
      return exprt();
    }

  case 'c':
    {
      u2 class_info_index = read_u2();
      return symbol_exprt(pool_entry(class_info_index).s);
    }

  case '@':
    {
      // TODO: return this wrapped in an exprt
      // another annotation, recursively
      annotationt annotation;
      rRuntimeAnnotation(annotation);
      return exprt();
    }

  case '[':
    {
      array_exprt values;
      u2 num_values=read_u2();
      for(std::size_t i=0; i<num_values; i++)
      {
        values.operands().push_back(get_relement_value());
      }
      return std::move(values);
    }

  case 's':
    {
      u2 const_value_index=read_u2();
      return string_constantt(pool_entry(const_value_index).s);
    }

  default:
    {
      u2 const_value_index=read_u2();
      return constant(const_value_index);
    }
  }
}

/// Corresponds to the element_value structure
/// Described in Java 8 specification 4.7.6
/// https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.7.6
/// Parses the InnerClasses attribute for the current parsed class,
/// which contains an array of information about its inner classes. We are
/// interested in getting information only for inner classes, which is
/// determined by checking if the parsed class matches any of the inner classes
/// in its inner class array. If the parsed class is not an inner class, then it
/// is ignored. When a parsed class is an inner class, the accessibility
/// information for the parsed class is overwritten, and the parsed class is
/// marked as an inner class.
void java_bytecode_parsert::rinner_classes_attribute(
  classt &parsed_class,
  const u4 &attribute_length)
{
  std::string name = parsed_class.name.c_str();
  u2 number_of_classes = read_u2();
  u4 number_of_bytes_to_be_read = number_of_classes * 8 + 2;
  INVARIANT(
    number_of_bytes_to_be_read == attribute_length,
    "The number of bytes to be read for the InnerClasses attribute does not "
    "match the attribute length.");

  const auto pool_entry_lambda = [this](u2 index) -> pool_entryt & {
    return pool_entry(index);
  };
  const auto remove_separator_char = [](std::string str, char ch) {
    str.erase(std::remove(str.begin(), str.end(), ch), str.end());
    return str;
  };

  for(int i = 0; i < number_of_classes; i++)
  {
    u2 inner_class_info_index = read_u2();
    u2 outer_class_info_index = read_u2();
    u2 inner_name_index = read_u2();
    u2 inner_class_access_flags = read_u2();

    std::string inner_class_info_name =
      class_infot(pool_entry(inner_class_info_index))
        .get_name(pool_entry_lambda);
    bool is_private = (inner_class_access_flags & ACC_PRIVATE) != 0;
    bool is_public = (inner_class_access_flags & ACC_PUBLIC) != 0;
    bool is_protected = (inner_class_access_flags & ACC_PROTECTED) != 0;
    bool is_static = (inner_class_access_flags & ACC_STATIC) != 0;

    // If the original parsed class name matches the inner class name,
    // the parsed class is an inner class, so overwrite the parsed class'
    // access information and mark it as an inner class.
    bool is_inner_class = remove_separator_char(id2string(parsed_class.name), '.') ==
      remove_separator_char(inner_class_info_name, '/');
    if(is_inner_class)
      parsed_class.is_inner_class = is_inner_class;
    if(!is_inner_class)
      continue;
    parsed_class.is_static_class = is_static;
    // This is a marker that a class is anonymous.
    if(inner_name_index == 0)
      parsed_class.is_anonymous_class = true;
    // Note that if outer_class_info_index == 0, the inner class is an anonymous
    // or local class, and is treated as private.
    if(outer_class_info_index == 0)
    {
      parsed_class.is_private = true;
      parsed_class.is_protected = false;
      parsed_class.is_public = false;
    }
    else
    {
      std::string outer_class_info_name =
        class_infot(pool_entry(outer_class_info_index))
          .get_name(pool_entry_lambda);
      parsed_class.outer_class =
        constant(outer_class_info_index).type().get(ID_C_base_name);
      parsed_class.is_private = is_private;
      parsed_class.is_protected = is_protected;
      parsed_class.is_public = is_public;
    }
  }
}

/// Corresponds to the element_value structure
/// Described in Java 8 specification 4.7.5
/// https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-4.html#jvms-4.7.5
/// Parses the Exceptions attribute for the current method,
/// and returns a vector of exceptions.
std::vector<irep_idt> java_bytecode_parsert::rexceptions_attribute()
{
  u2 number_of_exceptions = read_u2();

  std::vector<irep_idt> exceptions;
  for(size_t i = 0; i < number_of_exceptions; i++)
  {
    u2 exception_index_table = read_u2();
    const irep_idt exception_name =
      constant(exception_index_table).type().get(ID_C_base_name);
    exceptions.push_back(exception_name);
  }
  return exceptions;
}

void java_bytecode_parsert::rclass_attribute(classt &parsed_class)
{
  u2 attribute_name_index=read_u2();
  u4 attribute_length=read_u4();

  irep_idt attribute_name=pool_entry(attribute_name_index).s;

  if(attribute_name=="SourceFile")
  {
    u2 sourcefile_index=read_u2();
    irep_idt sourcefile_name;

    std::string fqn(id2string(parsed_class.name));
    size_t last_index=fqn.find_last_of(".");
    if(last_index==std::string::npos)
      sourcefile_name=pool_entry(sourcefile_index).s;
    else
    {
      std::string package_name=fqn.substr(0, last_index+1);
      std::replace(package_name.begin(), package_name.end(), '.', '/');
      const std::string &full_file_name=
        package_name+id2string(pool_entry(sourcefile_index).s);
      sourcefile_name=full_file_name;
    }

    for(methodst::iterator m_it=parsed_class.methods.begin();
        m_it!=parsed_class.methods.end();
        m_it++)
    {
      m_it->source_location.set_file(sourcefile_name);
      for(instructionst::iterator i_it=m_it->instructions.begin();
          i_it!=m_it->instructions.end();
          i_it++)
      {
        if(!i_it->source_location.get_line().empty())
          i_it->source_location.set_file(sourcefile_name);
      }
    }
  }
  else if(attribute_name=="Signature")
  {
    u2 signature_index=read_u2();
    parsed_class.signature=id2string(pool_entry(signature_index).s);
    get_dependencies_from_generic_parameters(
      parsed_class.signature.value(),
      parse_tree.class_refs);
  }
  else if(attribute_name=="RuntimeInvisibleAnnotations" ||
          attribute_name=="RuntimeVisibleAnnotations")
  {
    rRuntimeAnnotation_attribute(parsed_class.annotations);
  }
  else if(attribute_name == "BootstrapMethods")
  {
    // for this attribute
    // cf. https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.7.23
    INVARIANT(
      !parsed_class.attribute_bootstrapmethods_read,
      "only one BootstrapMethods argument is allowed in a class file");

    // mark as read in parsed class
    parsed_class.attribute_bootstrapmethods_read = true;
    read_bootstrapmethods_entry(parsed_class);
  }
  else if(attribute_name == "InnerClasses")
  {
    java_bytecode_parsert::rinner_classes_attribute(
      parsed_class, attribute_length);
  }
  else
    skip_bytes(attribute_length);
}

void java_bytecode_parsert::rmethods(classt &parsed_class)
{
  u2 methods_count=read_u2();

  for(std::size_t j=0; j<methods_count; j++)
    rmethod(parsed_class);
}

#define ACC_PUBLIC     0x0001
#define ACC_PRIVATE    0x0002
#define ACC_PROTECTED  0x0004
#define ACC_STATIC     0x0008
#define ACC_FINAL      0x0010
#define ACC_VARARGS    0x0080
#define ACC_SUPER      0x0020
#define ACC_VOLATILE   0x0040
#define ACC_TRANSIENT  0x0080
#define ACC_INTERFACE  0x0200
#define ACC_ABSTRACT   0x0400
#define ACC_SYNTHETIC  0x1000
#define ACC_ANNOTATION 0x2000
#define ACC_ENUM       0x4000

void java_bytecode_parsert::rmethod(classt &parsed_class)
{
  methodt &method=parsed_class.add_method();

  u2 access_flags=read_u2();
  u2 name_index=read_u2();
  u2 descriptor_index=read_u2();

  method.is_final=(access_flags&ACC_FINAL)!=0;
  method.is_static=(access_flags&ACC_STATIC)!=0;
  method.is_abstract=(access_flags&ACC_ABSTRACT)!=0;
  method.is_public=(access_flags&ACC_PUBLIC)!=0;
  method.is_protected=(access_flags&ACC_PROTECTED)!=0;
  method.is_private=(access_flags&ACC_PRIVATE)!=0;
  method.is_synchronized=(access_flags&ACC_SYNCHRONIZED)!=0;
  method.is_native=(access_flags&ACC_NATIVE)!=0;
  method.is_bridge = (access_flags & ACC_BRIDGE) != 0;
  method.is_varargs = (access_flags & ACC_VARARGS) != 0;
  method.name=pool_entry(name_index).s;
  method.base_name=pool_entry(name_index).s;
  method.descriptor=id2string(pool_entry(descriptor_index).s);

  const auto flags = (method.is_public ? 1 : 0) +
    (method.is_protected?1:0)+
    (method.is_private?1:0);
  DATA_INVARIANT(flags<=1, "at most one of public, protected, private");
  u2 attributes_count=read_u2();

  for(std::size_t j=0; j<attributes_count; j++)
    rmethod_attribute(method);
}

optionalt<java_bytecode_parse_treet>
java_bytecode_parse(std::istream &istream, message_handlert &message_handler)
{
  java_bytecode_parsert java_bytecode_parser;
  java_bytecode_parser.in=&istream;
  java_bytecode_parser.set_message_handler(message_handler);

  bool parser_result=java_bytecode_parser.parse();

  if(parser_result)
  {
    return {};
  }

  return std::move(java_bytecode_parser.parse_tree);
}

optionalt<java_bytecode_parse_treet>
java_bytecode_parse(const std::string &file, message_handlert &message_handler)
{
  std::ifstream in(file, std::ios::binary);

  if(!in)
  {
    messaget message(message_handler);
    message.error() << "failed to open input file `"
                    << file << '\'' << messaget::eom;
    return {};
  }

  return java_bytecode_parse(in, message_handler);
}

/// Parses the local variable type table of a method. The LVTT holds generic
/// type information for variables in the local variable table (LVT). At most as
/// many variables as present in the LVT can be in the LVTT.
void java_bytecode_parsert::parse_local_variable_type_table(methodt &method)
{
  u2 local_variable_type_table_length=read_u2();

  INVARIANT(
    local_variable_type_table_length<=method.local_variable_table.size(),
    "Local variable type table cannot have more elements "
    "than the local variable table.");
  for(std::size_t i=0; i<local_variable_type_table_length; i++)
  {
    u2 start_pc=read_u2();
    u2 length=read_u2();
    u2 name_index=read_u2();
    u2 signature_index=read_u2();
    u2 index=read_u2();

    bool found=false;
    for(auto &lvar : method.local_variable_table)
    {
      // compare to entry in LVT
      if(lvar.index==index &&
         lvar.name==pool_entry(name_index).s &&
         lvar.start_pc==start_pc &&
         lvar.length==length)
      {
        found=true;
        lvar.signature=id2string(pool_entry(signature_index).s);
        break;
      }
    }
    INVARIANT(
      found,
      "Entry in LocalVariableTypeTable must be present in LVT");
  }
}

/// Read method handle pointed to from constant pool entry at index, return type
/// of method handle and name if lambda function is found.
/// \param entry: the constant pool entry of the methodhandle_info structure
/// \returns: the method_handle type of the methodhandle_structure,
/// either for a recognized bootstrap method or for a lambda function
optionalt<java_bytecode_parsert::lambda_method_handlet>
java_bytecode_parsert::parse_method_handle(const method_handle_infot &entry)
{
  const std::function<pool_entryt &(u2)> pool_entry_lambda =
    [this](u2 index) -> pool_entryt & { return pool_entry(index); };

  const base_ref_infot &ref_entry = entry.get_reference(pool_entry_lambda);

  const class_infot &class_entry = ref_entry.get_class(pool_entry_lambda);
  const name_and_type_infot &name_and_type =
    ref_entry.get_name_and_type(pool_entry_lambda);

  std::string class_name = class_entry.get_name(pool_entry_lambda);
  // replace '.' for '$' (inner classes)
  std::replace(class_name.begin(), class_name.end(), '.', '$');
  // replace '/' for '.' (package)
  std::replace(class_name.begin(), class_name.end(), '/', '.');
  const std::string method_ref =
    class_name + "." + name_and_type.get_name(pool_entry_lambda) + ':' +
    name_and_type.get_descriptor(pool_entry_lambda);

  lambda_method_handlet lambda_method_handle;

  if(has_prefix(name_and_type.get_name(pool_entry_lambda), "lambda$"))
  {
    // names seem to be lambda$POSTFIX$NUM
    // where POSTFIX is FUN for a function name in which the lambda is define
    //                "static" when it is a static member of the class
    //                "new" when it is a class variable, instantiated in <init>
    lambda_method_handle.lambda_method_name =
      name_and_type.get_name(pool_entry_lambda);
    lambda_method_handle.lambda_method_ref = method_ref;
    lambda_method_handle.handle_type =
      method_handle_typet::LAMBDA_METHOD_HANDLE;

    return lambda_method_handle;
  }

  return {};
}

/// Read all entries of the `BootstrapMethods` attribute of a class file.
/// \param parsed_class: the class representation of the class file that is
/// currently parsed
void java_bytecode_parsert::read_bootstrapmethods_entry(classt &parsed_class)
{
  u2 num_bootstrap_methods = read_u2();
  for(size_t bootstrap_method_index = 0;
      bootstrap_method_index < num_bootstrap_methods;
      ++bootstrap_method_index)
  {
    u2 bootstrap_methodhandle_ref = read_u2();
    const pool_entryt &entry = pool_entry(bootstrap_methodhandle_ref);

    method_handle_infot method_handle{entry};

    u2 num_bootstrap_arguments = read_u2();
    debug() << "INFO: parse BootstrapMethod handle " << num_bootstrap_arguments
            << " #args" << eom;

    // read u2 values of entry into vector
    u2_valuest u2_values(num_bootstrap_arguments);
    for(size_t i = 0; i < num_bootstrap_arguments; i++)
      u2_values[i] = read_u2();

    // try parsing bootstrap method handle
    // each entry contains a MethodHandle structure
    // u2 tag
    // u2 reference kind which must be in the range from 1 to 9
    // u2 reference index into the constant pool
    //
    // reference kinds use the following
    // 1 to 4 must point to a CONSTANT_Fieldref structure
    // 5 or 8 must point to a CONSTANT_Methodref structure
    // 6 or 7 must point to a CONSTANT_Methodref or
    // CONSTANT_InterfaceMethodref structure, if the class file version
    // number is 52.0 or above, to a CONSTANT_Methodref only in the case
    // of less than 52.0
    // 9 must point to a CONSTANT_InterfaceMethodref structure

    // the index must point to a CONSTANT_String
    //                           CONSTANT_Class
    //                           CONSTANT_Integer
    //                           CONSTANT_Long
    //                           CONSTANT_Float
    //                           CONSTANT_Double
    //                           CONSTANT_MethodHandle
    //                           CONSTANT_MethodType

    // We read the three arguments here to see whether they correspond to
    // our hypotheses for this being a lambda function entry.

    // Need at least 3 arguments, the interface type, the method hanlde
    // and the method_type, otherwise it doesn't look like a call that we
    // understand
    if(num_bootstrap_arguments < 3)
    {
      store_unknown_method_handle(
        parsed_class, bootstrap_method_index, std::move(u2_values));
      debug()
        << "format of BootstrapMethods entry not recognized: too few arguments"
        << eom;
      continue;
    }

    u2 interface_type_index = u2_values[0];
    u2 method_handle_index = u2_values[1];
    u2 method_type_index = u2_values[2];

    // The additional arguments for the altmetafactory call are skipped,
    // as they are currently not used. We verify though that they are of
    // CONSTANT_Integer type, cases where this does not hold will be
    // analyzed further.
    bool recognized = true;
    for(size_t i = 3; i < num_bootstrap_arguments; i++)
    {
      u2 skipped_argument = u2_values[i];
      recognized &= pool_entry(skipped_argument).tag == CONSTANT_Integer;
    }

    if(!recognized)
    {
      debug() << "format of BootstrapMethods entry not recognized: extra "
                 "arguments of wrong type"
              << eom;
      store_unknown_method_handle(
        parsed_class, bootstrap_method_index, std::move(u2_values));
      continue;
    }

    const pool_entryt &interface_type_argument =
      pool_entry(interface_type_index);
    const pool_entryt &method_handle_argument = pool_entry(method_handle_index);
    const pool_entryt &method_type_argument = pool_entry(method_type_index);

    if(
      interface_type_argument.tag != CONSTANT_MethodType ||
      method_handle_argument.tag != CONSTANT_MethodHandle ||
      method_type_argument.tag != CONSTANT_MethodType)
    {
      debug() << "format of BootstrapMethods entry not recognized: arguments "
                 "wrong type"
              << eom;
      store_unknown_method_handle(
        parsed_class, bootstrap_method_index, std::move(u2_values));
      continue;
    }

    debug() << "INFO: parse lambda handle" << eom;
    optionalt<lambda_method_handlet> lambda_method_handle =
      parse_method_handle(method_handle_infot{method_handle_argument});

    if(!lambda_method_handle.has_value())
    {
      debug() << "format of BootstrapMethods entry not recognized: method "
                 "handle not recognised"
              << eom;
      store_unknown_method_handle(
        parsed_class, bootstrap_method_index, std::move(u2_values));
      continue;
    }

    // If parse_method_handle can't parse the lambda method, it should return {}
    POSTCONDITION(
      lambda_method_handle->handle_type != method_handle_typet::UNKNOWN_HANDLE);

    lambda_method_handle->interface_type =
      pool_entry(interface_type_argument.ref1).s;
    lambda_method_handle->method_type = pool_entry(method_type_argument.ref1).s;
    lambda_method_handle->u2_values = std::move(u2_values);
    debug() << "lambda function reference "
            << id2string(lambda_method_handle->lambda_method_name)
            << " in class \"" << parsed_class.name << "\""
            << "\n  interface type is "
            << id2string(pool_entry(interface_type_argument.ref1).s)
            << "\n  method type is "
            << id2string(pool_entry(method_type_argument.ref1).s) << eom;
    parsed_class.add_method_handle(
      bootstrap_method_index, *lambda_method_handle);
  }
}

/// Creates an unknown method handle and puts it into the parsed_class
/// \param parsed_class: The class whose bootstrap method handles we are using
/// \param bootstrap_method_index: The current index in the bootstrap entry
///   table
/// \param u2_values: The indices of the arguments for the call
void java_bytecode_parsert::store_unknown_method_handle(
  java_bytecode_parsert::classt &parsed_class,
  size_t bootstrap_method_index,
  java_bytecode_parsert::u2_valuest u2_values) const
{
  const lambda_method_handlet lambda_method_handle =
    lambda_method_handlet::create_unknown_handle(move(u2_values));
  parsed_class.add_method_handle(bootstrap_method_index, lambda_method_handle);
}
