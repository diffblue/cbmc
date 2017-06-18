/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_CLASS_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_CLASS_H

#include <util/expanding_vector.h>
#include <util/message.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/safe_pointer.h>
#include <analyses/cfg_dominators.h>
#include "java_bytecode_parse_tree.h"
#include "java_bytecode_convert_class.h"
#include "ci_lazy_methods.h"

#include <vector>
#include <list>

class symbol_tablet;
class symbolt;

class java_bytecode_convert_methodt:public messaget
{
public:
  java_bytecode_convert_methodt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    size_t _max_array_length,
    safe_pointer<ci_lazy_methodst> _lazy_methods,
    const character_refine_preprocesst &_character_preprocess):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    max_array_length(_max_array_length),
    lazy_methods(_lazy_methods),
    character_preprocess(_character_preprocess)
  {
  }

  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  typedef methodt::instructionst instructionst;
  typedef methodt::local_variable_tablet local_variable_tablet;
  typedef methodt::local_variablet local_variablet;

  void operator()(const symbolt &class_symbol, const methodt &method)
  {
    convert(class_symbol, method);
  }

protected:
  symbol_tablet &symbol_table;
  const size_t max_array_length;
  safe_pointer<ci_lazy_methodst> lazy_methods;

  irep_idt method_id;
  irep_idt current_method;
  typet method_return_type;
  character_refine_preprocesst character_preprocess;

public:
  struct holet
  {
    unsigned start_pc;
    unsigned length;
  };

  struct local_variable_with_holest
  {
    local_variablet var;
    std::vector<holet> holes;
  };

  typedef std::vector<local_variable_with_holest>
    local_variable_table_with_holest;

  class variablet
  {
  public:
    symbol_exprt symbol_expr;
    size_t start_pc;
    size_t length;
    bool is_parameter;
    std::vector<holet> holes;
    variablet() : symbol_expr(), start_pc(0), length(0), is_parameter(false) {}
  };

 protected:
  typedef std::vector<variablet> variablest;
  expanding_vectort<variablest> variables;
  std::set<symbol_exprt> used_local_names;
  bool method_has_this;

  enum instruction_sizet
  {
    INST_INDEX=2,
    INST_INDEX_CONST=3
  };

  codet get_array_bounds_check(
    const exprt &arraystruct,
    const exprt &idx,
    const source_locationt &original_sloc);

  // return corresponding reference of variable
  const variablet &find_variable_for_slot(
    size_t address,
    variablest &var_list);

  // JVM local variables
  enum variable_cast_argumentt
  {
    CAST_AS_NEEDED,
    NO_CAST
  };

  const exprt variable(
    const exprt &arg,
    char type_char,
    size_t address,
    variable_cast_argumentt do_cast);

  // temporary variables
  std::list<symbol_exprt> tmp_vars;

  symbol_exprt tmp_variable(const std::string &prefix, const typet &type);

  // JVM program locations
  irep_idt label(const irep_idt &address);

  // JVM Stack
  typedef std::vector<exprt> stackt;
  stackt stack;

  exprt::operandst pop(std::size_t n);

  void pop_residue(std::size_t n);
  void push(const exprt::operandst &o);

  bool is_constructor(const class_typet::methodt &method);

  struct converted_instructiont
  {
    converted_instructiont(
      const instructionst::const_iterator &it,
      const codet &_code):source(it), code(_code), done(false)
      {}

    instructionst::const_iterator source;
    std::list<unsigned> successors;
    std::set<unsigned> predecessors;
    codet code;
    stackt stack;
    bool done;
  };

public:
  typedef std::map<unsigned, converted_instructiont> address_mapt;
  typedef std::pair<const methodt &, const address_mapt &> method_with_amapt;
  typedef cfg_dominators_templatet<method_with_amapt, unsigned, false>
    java_cfg_dominatorst;

protected:
  void find_initialisers(
    local_variable_table_with_holest &vars,
    const address_mapt &amap,
    const java_cfg_dominatorst &doms);

  void find_initialisers_for_slot(
    local_variable_table_with_holest::iterator firstvar,
    local_variable_table_with_holest::iterator varlimit,
    const address_mapt &amap,
    const java_cfg_dominatorst &doms);

  void setup_local_variables(const methodt &m, const address_mapt &amap);

  struct block_tree_nodet
  {
    bool leaf;
    std::vector<unsigned> branch_addresses;
    std::vector<block_tree_nodet> branch;
    block_tree_nodet():leaf(false) {}
    explicit block_tree_nodet(bool l):leaf(l) {}
    static block_tree_nodet get_leaf() { return block_tree_nodet(true); }
  };

  static void replace_goto_target(
    codet &repl,
    const irep_idt &old_label,
    const irep_idt &new_label);

  code_blockt &get_block_for_pcrange(
    block_tree_nodet &tree,
    code_blockt &this_block,
    unsigned address_start,
    unsigned address_limit,
    unsigned next_block_start_address);

  code_blockt &get_or_create_block_for_pcrange(
    block_tree_nodet &tree,
    code_blockt &this_block,
    unsigned address_start,
    unsigned address_limit,
    unsigned next_block_start_address,
    const address_mapt &amap,
    bool allow_merge=true);

  // conversion
  void convert(const symbolt &class_symbol, const methodt &);

  codet convert_instructions(
    const methodt &,
    const code_typet &);

  const bytecode_infot &get_bytecode_info(const irep_idt &statement);

  enum class bytecode_write_typet { VARIABLE, ARRAY_REF, STATIC_FIELD, FIELD};
  void save_stack_entries(
    const std::string &,
    const typet &,
    code_blockt &,
    const bytecode_write_typet,
    const irep_idt &);
  void create_stack_tmp_var(
    const std::string &,
    const typet &,
    code_blockt &,
    exprt &);
};

#endif
