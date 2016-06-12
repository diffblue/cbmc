#include <iostream>
#include <functional>

#include <util/message.h>
#include <cbmc/bmc.h>

#include <java_bytecode/java_entry_point.h>
#include <test_gen/java_test_source_factory.h>
#include <test_gen/java_test_case_generator.h>

namespace
{
bool is_meta(const irep_idt &id)
{
  return std::string::npos != id2string(id).find("$assertionsDisabled");
}

inputst generate_inputs(const symbol_tablet &st, const goto_functionst &gf,
    const goto_tracet &trace)
{
  std::map<const irep_idt, exprt> result;
  for (const goto_trace_stept &step : trace.steps)
  {
    if (goto_trace_stept::ASSIGNMENT == step.type)
    {
      const exprt &lhs=step.full_lhs;
      if (ID_symbol == lhs.id())
      {
        const irep_idt &id=to_symbol_expr(lhs).get_identifier();
        if (st.has_symbol(id) && !is_meta(id))
          result.insert(std::make_pair(id, step.full_lhs_value));
      }
    }
  }
  return result;
}

const irep_idt &get_entry_function_id(const goto_functionst &gf)
{
  typedef goto_functionst::function_mapt function_mapt;
  const function_mapt &fm=gf.function_map;
  const irep_idt start(goto_functionst::entry_point());
  const function_mapt::const_iterator entry_func=fm.find(start);
  assert(fm.end() != entry_func);
  const goto_programt::instructionst &in=entry_func->second.body.instructions;
  typedef goto_programt::instructionst::const_reverse_iterator reverse_target;
  const reverse_target last=in.rbegin();
  const reverse_target end=in.rend();
  assert(end != last);
  const reverse_target call=std::next(last);
  assert(end != call);
  const code_function_callt &func_call=to_code_function_call(call->code);
  const exprt &func_expr=func_call.function();
  return to_symbol_expr(func_expr).get_identifier();
}

typedef std::function<
    std::string(const symbol_tablet &, const irep_idt &, const inputst &)> test_case_generatort;

int generate_test_case(optionst &options, const symbol_tablet &st,
    const goto_functionst &gf, bmct &bmc, const test_case_generatort generate)
{
  options.set_option("stop-on-fail", true);
  switch (bmc(gf))
  {
  case safety_checkert::SAFE:
    return TEST_CASE_FAIL;
  case safety_checkert::ERROR:
    return TEST_CASE_ERROR;
  case safety_checkert::UNSAFE:
  default:
  {
    const goto_tracet &trace=bmc.safety_checkert::error_trace;
    const inputst inputs(generate_inputs(st, gf, trace));
    const irep_idt &entry_func_id=get_entry_function_id(gf);
    const std::string source(generate(st, entry_func_id, inputs));
    const std::string file(options.get_option("test_case_file"));
    if (file.empty()) std::cout << source;
    else
    {
      std::ofstream ofs(file.c_str());
      ofs << source;
    }
    return TEST_CASE_SUCCESS;
  }
  }
}
}

int generate_java_test_case(optionst &o, const symbol_tablet &st,
    const goto_functionst &gf, bmct &bmc)
{
  try
  {
    return generate_test_case(o, st, gf, bmc,
        generate_java_test_case_from_inputs);
  } catch (const std::string &ex)
  {
    std::cerr << ex << std::endl;
    throw;
  }
}
