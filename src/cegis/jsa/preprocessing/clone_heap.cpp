/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <functional>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/clone_heap.h>

namespace
{
bool is_heap_type(const typet &type)
{
  if (ID_symbol != type.id()) return false;
  return to_symbol_type(type).get_identifier() == JSA_HEAP_TAG;
}

bool is_heap(const goto_programt::instructiont &instr)
{
  if (goto_program_instruction_typet::DECL != instr.type) return false;
  return is_heap_type(to_code_decl(instr.code).symbol().type());
}
}

const symbol_exprt &get_user_heap(const goto_functionst &gf)
{
  const goto_programt::instructionst &i=get_entry_body(gf).instructions;
  const goto_programt::const_targett end(i.end());
  const goto_programt::const_targett p=std::find_if(i.begin(), end, is_heap);
  assert(end != p);
  return to_symbol_expr(to_code_decl(p->code).symbol());
}

symbol_exprt get_queried_heap(const symbol_tablet &st)
{
  return st.lookup(get_cegis_meta_name(JSA_QUERIED_HEAP)).symbol_expr();
}

symbol_exprt get_org_heap(const symbol_tablet &st)
{
  return st.lookup(get_cegis_meta_name(JSA_ORG_HEAP)).symbol_expr();
}

void clone_heap(jsa_programt &prog)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos=prog.base_case;
  pos=insert_before_preserve_labels(body, pos);
  const symbol_typet heap_type(jsa_heap_type());
  declare_jsa_meta_variable(st, pos, JSA_QUERIED_HEAP, heap_type);
  jsa_assign(st, gf, pos, get_queried_heap(st), get_user_heap(gf));
  pos=insert_before_preserve_labels(body, prog.inductive_assumption);
  declare_jsa_meta_variable(st, pos, JSA_ORG_HEAP, heap_type);
  pos=jsa_assign(st, gf, pos, get_org_heap(st), get_user_heap(gf));
  const side_effect_expr_nondett nondet_heap(heap_type);
  pos=jsa_assign(st, gf, pos, get_user_heap(gf), nondet_heap);
  pos=assume_valid_heap(st, body, pos, address_of_exprt(get_user_heap(gf)));
  jsa_assign(st, gf, pos, get_queried_heap(st), get_org_heap(st));
  pos=jsa_assign(st, gf, prog.inductive_assumption, get_queried_heap(st), get_org_heap(st));
}

#define VALID_LIST JSA_PREFIX "assume_valid_list"
//#define VALID_IT JSA_PREFIX "assume_valid_iterator"
#define VALID_IT JSA_PREFIX "assume_valid_invariant_iterator" // XXX: TODO: Find a cleaner way.

namespace
{
std::vector<symbol_exprt> collect(goto_programt::targett first,
    const goto_programt::targett &last,
    const std::function<bool(const irep_idt &)> pred)
{
  std::vector<symbol_exprt> symbols;
  for (; first != last; ++first)
  {
    if (goto_program_instruction_typet::DECL != first->type) continue;
    const symbol_exprt symb(to_symbol_expr(to_code_decl(first->code).symbol()));
    if (pred(symb.get_identifier())) symbols.push_back(symb);
  }
  return symbols;
}

goto_programt::targett call_assume(const symbol_tablet &st,
    const char * const type, const exprt &heap, const exprt &arg,
    goto_programt &body, const goto_programt::targett &pos)
{
  const goto_programt::targett assume=body.insert_after(pos);
  assume->source_location=jsa_builtin_source_location();
  assume->type=goto_program_instruction_typet::FUNCTION_CALL;
  code_function_callt call;
  call.function()=st.lookup(type).symbol_expr();
  call.arguments().push_back(heap);
  call.arguments().push_back(arg);
  assume->code=call;
  return assume;
}

goto_programt::targett assume_lists_and_its_valid(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos, const exprt &heap_ptr)
{
  const goto_programt::targett first=body.instructions.begin();
  const std::vector<symbol_exprt> its(collect(first, pos, is_jsa_iterator));
  for (const symbol_exprt &it : its)
    pos=call_assume(st, VALID_IT, heap_ptr, it, body, pos);
  const std::vector<symbol_exprt> lists(collect(first, pos, is_jsa_list));
  for (const symbol_exprt &list : lists)
    pos=call_assume(st, VALID_LIST, heap_ptr, list, body, pos);
  return pos;
}
}

#define VALID_HEAP JSA_PREFIX "assume_valid_heap"

goto_programt::targett assume_valid_heap(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos, const exprt &heap_ptr)
{
  pos=body.insert_after(pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  code_function_callt call;
  call.function()=st.lookup(VALID_HEAP).symbol_expr();
  call.arguments().push_back(heap_ptr);
  pos->code=call;
  return assume_lists_and_its_valid(st, body, pos, heap_ptr);
}
