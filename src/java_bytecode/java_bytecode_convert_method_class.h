
#ifndef JBCM_CLASS_H
#define JBCM_CLASS_H

#include <util/expanding_vector.h>
#include <util/message.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <analyses/cfg_dominators.h>
#include "java_bytecode_parse_tree.h"

#include <vector>
#include <list>

class symbol_tablet;
class symbolt;

class java_bytecode_convert_methodt:public messaget
{
public:
  java_bytecode_convert_methodt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler);

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
  irep_idt method_id;
  symbol_tablet &symbol_table;

  irep_idt current_method;
  typet method_return_type;

public:
  struct holet {
    unsigned start_pc;
    unsigned length;
  };

  struct local_variable_with_holest
  {
    local_variablet var;
    std::vector<holet> holes;
  };

  typedef std::vector<local_variable_with_holest> local_variable_table_with_holest;

protected:
  class variablet
  {
  public:
    symbol_exprt symbol_expr;
    size_t start_pc;
    size_t length;
    bool is_parameter;
    std::vector<holet> holes;
    variablet() : symbol_expr(), is_parameter(false) {}
  };

  typedef std::vector<variablet> variablest;
  expanding_vector<variablest> variables;
  std::set<symbol_exprt> used_local_names;
  bool method_has_this;

  // return corresponding reference of variable
  const variablet &find_variable_for_slot(size_t address, variablest &var_list);

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

  void push(const exprt::operandst &o);

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
  typedef cfg_dominators_templatet<const address_mapt,unsigned,false> java_cfg_dominatorst;

protected:

  void find_initialisers(
    local_variable_table_with_holest& vars,
    const address_mapt& amap,
    const java_cfg_dominatorst& doms);

  void find_initialisers_for_slot(
    local_variable_table_with_holest::iterator firstvar,
    local_variable_table_with_holest::iterator varlimit,
    const address_mapt& amap,
    const java_cfg_dominatorst& doms);

  void setup_local_variables(const methodt& m, const address_mapt& amap);

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
  void convert(const instructiont &);

  codet convert_instructions(
    const methodt &,
    const code_typet &);

  const bytecode_infot &get_bytecode_info(const irep_idt &statement);
};

#endif
