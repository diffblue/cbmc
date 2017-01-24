#include <util/bv_arithmetic.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_trace.h>

#include <cegis/instrument/meta_variables.h>
#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/jsa_genetic_solution.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/converters/solution.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/learn/extract_candidate.h>

namespace
{
typedef std::pair<size_t, array_exprt> encoded_programt;
typedef std::vector<encoded_programt> encoded_programst;

inline bool is_integer(const std::string & s)
{
  if (s.empty() || (!isdigit(s[0]) && s[0] != '-' && s[0] != '+')) return false;
  char *p;
  long result=strtol(s.c_str(), &p, 10);
  (void)result; // unused as just used for testing string format
  return *p==0;
}

bool is_prog_name(const std::string &var_name, const std::string &prefix)
{
  const std::string::size_type prefix_size=prefix.size();
  if (var_name.substr(0, prefix_size) != prefix) return false;
  const std::string suffix(var_name.substr(prefix_size));
  return suffix.empty() || is_integer(suffix);
}

bool find_prog(encoded_programt &result,
    goto_tracet::stepst::const_iterator &first,
    const goto_tracet::stepst::const_iterator &last, const std::string &name)
{
  const goto_tracet::stepst::const_iterator origin(first);
  const std::string prefix(get_cegis_meta_name(name));
  for (; first != last; ++first)
  {
    if (goto_trace_stept::DECL != first->type) continue;
    const std::string &var_name=id2string(first->lhs_object.get_identifier());
    if (!is_prog_name(var_name, prefix)) continue;
    std::string sz_name(var_name);
    sz_name+= JSA_SIZE_SUFFIX;
    goto_tracet::stepst::const_iterator sz;
    for (sz=first; id2string(sz->lhs_object.get_identifier()) != sz_name; --sz)
      assert(sz != origin);
    const bv_arithmetict bv(sz->full_lhs_value);
    result.first=bv.to_integer().to_ulong();
    result.second=to_array_expr(first++->full_lhs_value);
    return true;
  }
  return false;
}

std::vector<__CPROVER_jsa_pred_instructiont> to_genetic_pred(const encoded_programt &prog)
{
  std::vector<__CPROVER_jsa_pred_instructiont> result(prog.first);
  const array_exprt::operandst &ops=prog.second.operands();
  for (size_t i=0; i < result.size(); ++i)
  {
    const struct_exprt::operandst &members=to_struct_expr(ops[i]).operands();
    assert(members.size() == 4u);
    __CPROVER_jsa_pred_instruction &instr=result[i];
    struct_exprt::operandst::const_iterator member=members.begin();
    instr.opcode=bv_arithmetict(*member++).to_integer().to_ulong();
    instr.result_op=bv_arithmetict(*member++).to_integer().to_ulong();
    instr.op0=bv_arithmetict(*member++).to_integer().to_ulong();
    instr.op1=bv_arithmetict(*member).to_integer().to_ulong();
  }
  return result;
}

std::vector<__CPROVER_jsa_query_instructiont> to_genetic_query(const encoded_programt &prog)
{
  std::vector<__CPROVER_jsa_query_instructiont> result(prog.first);
  const array_exprt::operandst &ops=prog.second.operands();
  for (size_t i=0; i < result.size(); ++i)
  {
    const struct_exprt::operandst &members=to_struct_expr(ops[i]).operands();
    assert(members.size() == 3u);
    __CPROVER_jsa_query_instructiont &instr=result[i];
    struct_exprt::operandst::const_iterator member=members.begin();
    instr.opcode=bv_arithmetict(*member++).to_integer().to_ulong();
    instr.op0=bv_arithmetict(*member++).to_integer().to_ulong();
    instr.op1=bv_arithmetict(*member).to_integer().to_ulong();
  }
  return result;
}

std::vector<__CPROVER_jsa_invariant_instructiont> to_genetic_inv(const encoded_programt &prog)
{
  std::vector<__CPROVER_jsa_invariant_instructiont> result(prog.first);
  const array_exprt::operandst &ops=prog.second.operands();
  for (size_t i=0; i < result.size(); ++i)
  {
    const struct_exprt::operandst &members=to_struct_expr(ops[i]).operands();
    assert(members.size() == 1u);
    __CPROVER_jsa_invariant_instructiont &instr=result[i];
    instr.opcode=bv_arithmetict(members.front()).to_integer().to_ulong();
  }
  return result;
}
}

void extract_jsa_genetic_candidate(jsa_genetic_solutiont &solution,
    const jsa_programt &prog, const goto_tracet &trace)
{
  goto_tracet::stepst::const_iterator first(trace.steps.begin());
  const goto_tracet::stepst::const_iterator last(trace.steps.end());
  goto_tracet::stepst::const_iterator last_pred;
  encoded_programt tmp;
  while (find_prog(tmp, first, last, JSA_PRED_PREFIX))
  {
    solution.predicates.push_back(to_genetic_pred(tmp));
    last_pred=first;
  }
  first=last_pred;
  assert(find_prog(tmp, first, last, JSA_QUERY));
  solution.query=to_genetic_query(tmp);
  assert(find_prog(tmp, first, last, JSA_INV));
  solution.invariant=to_genetic_inv(tmp);
}

namespace
{
void post_process(jsa_genetic_solutiont &solution, const pred_op_idst &pred_ops,
    const pred_op_idst &result_pred_ops, const size_t max_size)
{
  // Unused predicates need to be zeroed.
  const __CPROVER_jsa_pred_instructiont zero = { 0, 0, 0, 0 };
  const size_t num_ops=pred_ops.size();
  for (jsa_genetic_solutiont::predicatest::value_type &pred : solution.predicates)
    for (const __CPROVER_jsa_pred_instructiont &instr : pred)
      if (instr.opcode >= __CPROVER_JSA_NUM_PRED_INSTRUCTIONS ||
          instr.result_op >= result_pred_ops.size() ||
          instr.op0 >= num_ops || instr.op1 >= num_ops)
      {
        std::fill(pred.begin(), pred.end(), zero);
        break;
      }
}
}

void extract_jsa_candidate(jsa_solutiont &solution, const jsa_programt &prog,
    const goto_tracet &trace, const pred_op_idst &pred_ops,
    const pred_op_idst &result_pred_ops, const size_t max_size)
{
  jsa_genetic_solutiont tmp;
  extract_jsa_genetic_candidate(tmp, prog, trace);
  post_process(tmp, pred_ops, result_pred_ops, max_size);
  solution=convert(tmp, prog);
}
