/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/cprover_library.h>
#include <ansi-c/c_types.h>
#include <util/bv_arithmetic.h>
#include <goto-programs/goto_convert_functions.h>
#include <linking/linking.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_synthesis_library.h>

#define CPROVER_INIT "__CPROVER_initialize"
#define JSA_LIB "__CPROVER_jsa_synthesise"

namespace
{
void add_placenholder(symbol_tablet &st, const irep_idt &id)
{
  if (st.has_symbol(id)) return;
  symbolt symbol;
  symbol.name=id;
  symbol.base_name=symbol.name;
  symbol.pretty_name=symbol.base_name;
  symbol.type=signed_int_type();
  symbol.is_lvalue=true;
  symbol.mode=ID_C;
  symbol.module=JSA_MODULE;
  st.add(symbol);
}

std::string get_array_size(const typet &type)
{
  const irep_idt &type_id=type.id();
  if (ID_array == type_id)
  {
    const bv_arithmetict bv(to_array_type(type).size());
    return std::to_string(bv.to_integer().to_ulong());
  }
  assert(ID_pointer == type_id);
  return "0u";
}

std::string get_sizes(const symbol_tablet &st)
{
  const namespacet ns(st);
  const typet &type=ns.follow(st.lookup(JSA_HEAP_TAG).type);
  const struct_typet &struct_type=to_struct_type(type);
  std::string sizes("#define __CPROVER_JSA_MAX_CONCRETE_NODES ");
  sizes+=get_array_size(struct_type.get_component("concrete_nodes").type());
  sizes+="\n#define __CPROVER_JSA_MAX_ABSTRACT_NODES ";
  sizes+=get_array_size(struct_type.get_component("abstract_nodes").type());
  sizes+="\n#define __CPROVER_JSA_MAX_ITERATORS ";
  sizes+=get_array_size(struct_type.get_component("iterators").type());
  sizes+="\n#define __CPROVER_JSA_MAX_LISTS ";
  sizes+=get_array_size(struct_type.get_component("list_head_nodes").type());
  return sizes+='\n';
}

std::vector<irep_idt> get_functions(const symbol_tablet &st)
{
  std::vector<irep_idt> functions;
  for (const symbol_tablet::symbolst::value_type &symbol : st.symbols)
    if (ID_code == symbol.second.type.id()) functions.push_back(symbol.first);
  return functions;
}

bool is_jsa_constant(const symbolt &symbol)
{
  if (!symbol.is_static_lifetime) return false;
  const std::string &name=id2string(symbol.name);
  return std::string::npos != name.find(JSA_CONSTANT_PREFIX)
      || std::string::npos != name.find(JSA_STATIC_META_VAR_PREFIX);
}

void zero_new_global_vars(const symbol_tablet &st, goto_functionst &gf)
{
  goto_functionst::function_mapt &fm=gf.function_map;
  const goto_functionst::function_mapt::iterator it=fm.find(CPROVER_INIT);
  assert(fm.end() != it);
  goto_functionst::goto_functiont &init=it->second;
  assert(init.body_available());
  goto_programt &body=init.body;
  goto_programt::targett pos=std::prev(body.instructions.end(), 2);
  const source_locationt loc(jsa_builtin_source_location());
  const namespacet ns(st);
  for (const symbol_tablet::symbolst::value_type &symbol : st.symbols)
    if (is_jsa_constant(symbol.second))
    {
      pos=body.insert_after(pos);
      pos->type=goto_program_instruction_typet::ASSIGN;
      pos->source_location=loc;
      const symbol_exprt lhs(ns.lookup(symbol.first).symbol_expr());
      const exprt rhs(zero_initializer(lhs.type(), loc, ns));
      pos->code=code_assignt(lhs, rhs);
    }
}

bool is_const(const symbol_tablet &st, const goto_programt::instructiont &instr)
{
  return is_jsa_const(st.lookup(get_affected_variable(instr)).symbol_expr());
}
}

void add_jsa_library(jsa_programt &prog, const size_t max_sz,
    const goto_programt::targetst &pred_op_locations)
{
  std::string library_text("#define JSA_SYNTHESIS_H_");
  library_text+="\n#define __CPROVER_JSA_MAX_QUERY_SIZE ";
  library_text+=std::to_string(max_sz + 1);
  library_text+="\n#define __CPROVER_JSA_MAX_PRED_SIZE ";
  library_text+=std::to_string(max_sz);
  library_text+="\n#define __CPROVER_JSA_NUM_PRED_OPS ";
  const size_t num_pred_ops=pred_op_locations.size();
  library_text+=std::to_string(num_pred_ops);
  symbol_tablet &st=prog.st;
  const size_t num_result_pred_ops=std::count_if(pred_op_locations.begin(),
      pred_op_locations.end(), [&st](const goto_programt::targett &target)
      { return !is_const(st, *target);});
  library_text+="\n#define __CPROVER_JSA_NUM_PRED_RESULT_OPS ";
  library_text+=std::to_string(num_result_pred_ops);
  library_text+='\n';
  library_text+=get_sizes(prog.st);
  const std::set<irep_idt> functions={ JSA_LIB };
  symbol_tablet blank;
  add_placenholder(blank, JSA_LIB);
  library_text+=get_cprover_library_text(functions, blank);
  blank.clear();
  null_message_handlert msg;
  add_library(library_text, blank, msg);

  assert(!linking(st, blank, msg));
  goto_functionst &gf=prog.gf;
  const std::vector<irep_idt> new_funcs(get_functions(blank));
  for (const irep_idt &func_name : new_funcs)
    goto_convert(func_name, st, gf, msg);
  zero_new_global_vars(blank, gf);
  gf.compute_loop_numbers();
  gf.update();
}
