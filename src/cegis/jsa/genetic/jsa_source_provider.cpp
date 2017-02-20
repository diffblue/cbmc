/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/options.h>
#include <util/substitute.h>
#include <goto-programs/remove_returns.h>
#include <goto-instrument/dump_c.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/jsa/value/jsa_genetic_synthesis.h>
#include <cegis/jsa/options/jsa_program_info.h>
#include <cegis/jsa/instrument/temps_helper.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>
#include <cegis/jsa/genetic/jsa_source_provider.h>

jsa_source_providert::jsa_source_providert(jsa_symex_learnt &lcfg) :
    lcfg(lcfg)
{
}

#define RETURN_VALUE_ASSIGNMENT RETURN_VALUE_SUFFIX" ="
#define JUMP_BUFFER "__CPROVER_jsa_jump_buffer"
#define TEST_SIGNATURE "int " CEGIS_FITNESS_TEST_FUNC \
  "(const __CPROVER_jsa_index_t __CPROVER_jsa_query_size, " \
      "const __CPROVER_jsa_query_instructiont * const __CPROVER_jsa_query, " \
      "const __CPROVER_jsa_index_t __CPROVER_jsa_invariant_size, " \
      "const __CPROVER_jsa_invariant_instructiont * const __CPROVER_jsa_invariant, " \
      "const __CPROVER_jsa_index_t * const __CPROVER_jsa_predicate_sizes, " \
      "const __CPROVER_jsa_pred_instructiont **__CPROVER_jsa_predicates, " \
      "const __CPROVER_jsa_abstract_heapt *__CPROVER_jsa_counterexample_heaps, " \
      "const __CPROVER_jsa_word_t *__CPROVER_jsa_counterexample_words)"
#define CE_ASSIGNMENT_MARKER "= __CPROVER_jsa_ce_array___CPROVER_jsa_predicate_ce_marker_"

namespace
{
void add_jsa_defines(std::string &result, const jsa_symex_learnt &lcfg)
{
  result+="#define __CPROVER_assume(c) __CPROVER_jsa_assume(c)\n"
      "#define __CPROVER_JSA_DYNAMIC_TEST_RUNNER\n"
      "#define __CPROVER_JSA_MAX_CONCRETE_NODES ";
  result+=std::to_string(__CPROVER_JSA_MAX_CONCRETE_NODES);
  result+="\n#define __CPROVER_JSA_MAX_ABSTRACT_NODES ";
  result+=std::to_string(__CPROVER_JSA_MAX_ABSTRACT_NODES);
  result+="\n#define JSA_SYNTHESIS_H_\n"
      "#define __CPROVER_JSA_DEFINE_TRANSFORMERS\n";
  result+="\n#define __CPROVER_JSA_MAX_LISTS ";
  result+=std::to_string(__CPROVER_JSA_MAX_LISTS);
  result+="\n#define __CPROVER_JSA_MAX_NODES_PER_CE_LIST ";
  result+=std::to_string(__CPROVER_JSA_MAX_NODES_PER_CE_LIST);
  result+="\n#define __CPROVER_JSA_MAX_ITERATORS ";
  result+=std::to_string(__CPROVER_JSA_MAX_ITERATORS);
  result+="\n#define __CPROVER_JSA_MAX_QUERY_SIZE ";
  result+=std::to_string(__CPROVER_JSA_MAX_QUERY_SIZE);
  result+="\n#define __CPROVER_JSA_MAX_PRED_SIZE ";
  result+=std::to_string(__CPROVER_JSA_MAX_PRED_SIZE);
  result+="\n#define __CPROVER_JSA_NUM_PRED_OPS ";
  result+=std::to_string(__CPROVER_JSA_NUM_PRED_OPS);
  result+="\n#define __CPROVER_JSA_NUM_PRED_RESULT_OPS ";
  result+=std::to_string(__CPROVER_JSA_NUM_PRED_RESULT_OPS);
  result+="\n#define __CPROVER_JSA_NUM_PREDS ";
  result+=std::to_string(__CPROVER_JSA_NUM_PREDS);
  result+="\n\n";
}

void add_includes_and_globals(std::string &result)
{
  result+="#include <stdlib.h>\n\n"
      "#include <ansi-c/library/jsa.h>\n\n";
  result+="jmp_buf " JUMP_BUFFER";\n\n";
}

void add_temp_clean(std::string &result, const symbol_tablet &st)
{
  result+="void __CPROVER_jsa_internal__clear_temps(void)\n{\n";
  const size_t num_temps=count_tmps(st);
  assert(num_temps >= 1);
  for(size_t i=1; i <= num_temps; ++i)
  {
    result+="  *" JSA_PRED_RES_OPS "[";
    result+=std::to_string(i);
    result+="]=0;\n";
  }
  result+="}\n\n";
}

void add_main_body(std::string &result, const jsa_symex_learnt &lcfg)
{
  const goto_functionst &gf=lcfg.get_goto_functions();
  const goto_functionst::function_mapt &fm=gf.function_map;
  goto_functionst entry_only;
  const irep_idt entry_id(goto_functionst::entry_point());
  const goto_functionst::function_mapt::const_iterator it=fm.find(entry_id);
  entry_only.function_map[entry_id].copy_from(it->second);
  const namespacet ns(lcfg.get_symbol_table());
  std::ostringstream oss;
  dump_c(entry_only, false, ns, oss);
  const std::string main_body(oss.str());
  result+=
    main_body.substr(
      main_body.find(std::string("void ")+id2string(gf.entry_point())));
}

void fix_return_values(std::string &result)
{
  std::string::size_type pos=result.find(RETURN_VALUE_ASSIGNMENT);
  while(std::string::npos != pos)
  {
    const std::string::size_type start=result.rfind(' ', pos);
    const std::string::size_type value=result.find('=', pos);
    const std::string::size_type end=result.find(';', pos);
    std::string return_statement=" return";
    return_statement+=result.substr(value + 1, end - value);
    result.replace(start, end, return_statement);
    pos=result.find(RETURN_VALUE_ASSIGNMENT, start);
  }
  pos=result.find(RETURN_VALUE_SUFFIX);
  while(std::string::npos != pos)
  {
    const std::string::size_type end=result.rfind("= ", pos);
    const std::string::size_type start=result.rfind(' ', end - 2);
    std::string var_name=result.substr(start + 1, end - start);
    var_name+=' ';
    const std::string::size_type prev_end=result.rfind('\n', start);
    const std::string::size_type prev_start=result.rfind("  ", prev_end);
    const std::string::size_type line_end=result.find('\n', prev_end + 1);
    result.erase(prev_end, line_end - prev_end);
    result.insert(prev_start + 2, var_name);
    pos=result.find(RETURN_VALUE_SUFFIX, prev_start);
  }
  substitute(result, "assert((_Bool)0)", "return EXIT_SUCCESS");
  substitute(result, "\n  return 0;", "");
}

void add_facade_function(const goto_functionst &gf, std::string &result)
{
  std::ostringstream start_sig;
  start_sig << "void " << gf.entry_point() << "(void)";
  substitute(result, start_sig.str(), TEST_SIGNATURE);
  const std::string::size_type pos=result.find("  __CPROVER_initialize();");
  result.insert(pos, "  if (setjmp(" JUMP_BUFFER")) return EXIT_FAILURE;\n");
}

void remove_line_with(std::string &result, const std::string &value)
{
  const std::string::size_type pos=result.find(value);
  const std::string::size_type start=result.rfind('\n', pos);
  const std::string::size_type end=result.find('\n', pos);
  result.erase(start, end - start);
}

void remove_predicates(std::string &result, const size_t num_preds)
{
  for(size_t i=0; i < num_preds; ++i)
  {
    std::string base_name="__CPROVER_jsa_predicate_";
    base_name+=std::to_string(i);
    std::string size_var_name(base_name);
    size_var_name+="_size;";
    remove_line_with(result, size_var_name);
    std::string var_name(base_name);
    var_name+='[';
    remove_line_with(result, var_name);
  }
}

void declare_predicates(std::string &result, const size_t num_preds,
    const std::string::size_type pos)
{
  std::string source;
  for(size_t i=0; i < num_preds; ++i)
  {
    std::string base_name("__CPROVER_jsa_predicate_");
    base_name+=std::to_string(i);
    source+="  __CPROVER_jsa_index_t ";
    source+=base_name;
    source+="_size=__CPROVER_jsa_predicate_sizes[";
    source+=std::to_string(i);
    source+="];\n";
    source+="  const __CPROVER_jsa_pred_instructiont * const ";
    source+=base_name;
    source+="=__CPROVER_jsa_predicates[";
    source+=std::to_string(i);
    source+="];\n";
  }
  result.insert(pos, source);
}

void insert_solution(std::string &result, const jsa_symex_learnt &lcfg)
{
  const std::string::size_type pos=result.find("  __CPROVER_initialize();\n");
  const size_t num_preds=get_num_jsa_preds(lcfg.get_symbol_table());
  remove_predicates(result, num_preds);
  declare_predicates(result, num_preds, pos);
  remove_line_with(result, "__CPROVER_jsa_query_size;");
  remove_line_with(result, "__CPROVER_jsa_query[");
  remove_line_with(result, "__CPROVER_jsa_invariant_size;");
  remove_line_with(result, "__CPROVER_jsa_invariant[");
}

bool is_heap(const std::string &line)
{
  return std::string::npos != line.find("heap");
}

void insert_counterexample(std::string &result)
{
  std::string::size_type pos=result.find(CE_ASSIGNMENT_MARKER);
  size_t heap_count=0;
  size_t word_count=0;
  while(std::string::npos != pos)
  {
    const std::string::size_type line_start=result.rfind("  ", pos);
    const std::string::size_type line_end=result.find('\n', pos);
    const std::string line(result.substr(line_start, line_end - line_start));
    const std::string::size_type stmt_end=result.find(';', pos);
    std::string value("= ");
    if(is_heap(line))
    {
      value+="__CPROVER_jsa_counterexample_heaps[";
      value+=std::to_string(heap_count++);
    } else
    {
      value+="__CPROVER_jsa_counterexample_words[";
      value+=std::to_string(word_count++);
    }
    value+=']';
    result.replace(pos, stmt_end - pos, value);
    pos=result.find(CE_ASSIGNMENT_MARKER, line_start);
  }
}

void cleanup(std::string &result)
{
  substitute(result, "  __CPROVER_initialize();\n", "");
  result+="\n}\n";
}
}

const std::string &jsa_source_providert::operator ()()
{
  if(!source.empty()) return source;
  add_jsa_defines(source, lcfg);
  add_includes_and_globals(source);
  add_temp_clean(source, lcfg.get_symbol_table());
  add_main_body(source, lcfg);
  fix_return_values(source);
  add_facade_function(lcfg.get_goto_functions(), source);
  insert_solution(source, lcfg);
  insert_counterexample(source);
  cleanup(source);
  return source;
}
