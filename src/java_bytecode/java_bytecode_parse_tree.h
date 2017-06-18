/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSE_TREE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSE_TREE_H

#include <set>

#include <util/std_code.h>
#include <util/std_types.h>

#include "bytecode_info.h"

class java_bytecode_parse_treet
{
public:
  class annotationt
  {
  public:
    typet type;

    class element_value_pairt
    {
    public:
      irep_idt element_name;
      exprt value;
      void output(std::ostream &) const;
    };

    using element_value_pairst = std::vector<element_value_pairt>;
    element_value_pairst element_value_pairs;

    void output(std::ostream &) const;
  };

  using annotationst = std::vector<annotationt>;

  class instructiont
  {
  public:
    source_locationt source_location;
    unsigned address;
    irep_idt statement;
    using argst = std::vector<exprt>;
    argst args;
  };

  class membert
  {
  public:
    std::string signature;
    irep_idt name;
    bool is_public, is_protected, is_private, is_static, is_final;
    annotationst annotations;

    virtual void output(std::ostream &out) const = 0;

    membert():
      is_public(false), is_protected(false), is_private(false),
      is_static(false), is_final(false)
    {
    }
  };

  class methodt:public membert
  {
  public:
    irep_idt base_name;
    bool is_native, is_abstract, is_synchronized;
    source_locationt source_location;

    using instructionst = std::vector<instructiont>;
    instructionst instructions;

    instructiont &add_instruction()
    {
      instructions.push_back(instructiont());
      return instructions.back();
    }

    struct exceptiont
    {
    public:
      std::size_t start_pc;
      std::size_t end_pc;
      std::size_t handler_pc;
      symbol_typet catch_type;
    };

    using exception_tablet = std::vector<exceptiont>;
    exception_tablet exception_table;

    class local_variablet
    {
    public:
      irep_idt name;
      std::string signature;
      std::size_t index;
      std::size_t start_pc;
      std::size_t length;
    };

    using local_variable_tablet = std::vector<local_variablet>;
    local_variable_tablet local_variable_table;

    class verification_type_infot
    {
    public:
      enum verification_type_info_type { TOP, INTEGER, FLOAT, LONG, DOUBLE,
                                         ITEM_NULL, UNINITIALIZED_THIS,
                                         OBJECT, UNINITIALIZED};
      verification_type_info_type type;
      u1 tag;
      u2 cpool_index;
      u2 offset;
    };

    class stack_map_table_entryt
    {
    public:
      enum stack_frame_type
      {
        SAME, SAME_LOCALS_ONE_STACK, SAME_LOCALS_ONE_STACK_EXTENDED,
        CHOP, SAME_EXTENDED, APPEND, FULL
      };
      stack_frame_type type;
      size_t offset_delta;
      size_t chops;
      size_t appends;

      using local_verification_type_infot = std::vector<verification_type_infot>;
      using stack_verification_type_infot = std::vector<verification_type_infot>;

      local_verification_type_infot locals;
      stack_verification_type_infot stack;
    };

    using stack_map_tablet = std::vector<stack_map_table_entryt>;
    stack_map_tablet stack_map_table;

    virtual void output(std::ostream &out) const;

    methodt():
      is_native(false),
      is_abstract(false),
      is_synchronized(false)
    {
    }
  };

  class fieldt:public membert
  {
  public:
    virtual void output(std::ostream &out) const;
    bool is_enum;
  };

  class classt
  {
  public:
    irep_idt name, extends;
    bool is_abstract=false;
    bool is_enum=false;
    size_t enum_elements=0;

    using implementst = std::list<irep_idt>;
    implementst implements;

    using fieldst = std::list<fieldt>;
    using methodst = std::list<methodt>;
    fieldst fields;
    methodst methods;
    annotationst annotations;

    fieldt &add_field()
    {
      fields.push_back(fieldt());
      return fields.back();
    }

    methodt &add_method()
    {
      methods.push_back(methodt());
      return methods.back();
    }

    void output(std::ostream &out) const;

    void swap(classt &other);
  };

  classt parsed_class;

  void swap(java_bytecode_parse_treet &other)
  {
    other.parsed_class.swap(parsed_class);
    other.class_refs.swap(class_refs);
    std::swap(loading_successful, other.loading_successful);
  }

  void output(std::ostream &out) const;

  using class_refst = std::set<irep_idt>;
  class_refst class_refs;

  bool loading_successful;

  java_bytecode_parse_treet():loading_successful(false)
  {
  }
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_PARSE_TREE_H
