/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cstring>

#include <util/substitute.h>

#include <goto-instrument/dump_c.h>

#include <cegis/genetic/program_individual_test_runner_helper.h>
#include <cegis/instrument/cegis_library.h>
#include <cegis/instrument/literals.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/invariant/fitness/concrete_fitness_source_provider.h>

namespace
{
void add_assume_implementation(std::string &source)
{
  source+=
      "#define " CEGIS_PREFIX "assert(constraint) if(constraint) { return 0; } else { return 1; }\n";
  source+="#define __CPROVER_assume(constraint) \n";
  source+=
      "#define " CEGIS_PREFIX "execute_assume(constraint) if (!(constraint)) { return 1; }\n";
}

void add_danger_execute(std::string &source, const size_t num_vars,
    const size_t num_consts, const size_t max_prog_size,
    const std::string &exec_func_name)
{
  std::string text=get_cegis_library_text(num_vars, num_consts, max_prog_size,
      exec_func_name);
  substitute(text, "#define opcode program[i].opcode",
      "const opcodet opcode=program[i].opcode;");
  substitute(text, "#line 1 \"<builtin-library>\"",
      "//#line 2 \"<builtin-library>\"");
  substitute(text, "#line 1 \"<builtin-library-__CPROVER_danger_execute>\"",
      "//#line 2 \"<builtin-library-__CPROVER_danger_execute>\"");
  const char result_op[]=
      "    *(unsigned int *)" CEGIS_RESULT_OPS "[i]=result;\n  }\n";
  const std::string::size_type pos=text.find(result_op);
  assert(std::string::npos != pos);
  text.insert(pos + strlen(result_op),
      "if (size <= 0 || size >= " CEGIS_PREFIX "max_solution_size) return 0;\n"
      "int diff=" CEGIS_PREFIX "max_solution_size-size;\n"
      "for (int i = size-1; i >= 0; --i) {\n"
      "  *(unsigned int *)" CEGIS_RESULT_OPS "[i+diff]=*(unsigned int *)" CEGIS_RESULT_OPS "[i];\n"
      "}\n"
      "return 0;\n");
  substitute(text, "__CPROVER_assume(op0_ptr && op1_ptr && op2_ptr)",
  CEGIS_PREFIX "execute_assume(op0_ptr && op1_ptr && op2_ptr)");
  substitute(text, "__CPROVER_assume((opcode != 19 && opcode != 20) || op1)",
  CEGIS_PREFIX "execute_assume(opcode != 19 && opcode != 20 || op1)");
  substitute(text, "void __CPROVER_danger_execute(",
      "int __CPROVER_danger_execute_impl(");
  source+=text;
  source+=
      "#define __CPROVER_danger_execute(prog, size) if (__CPROVER_danger_execute_impl(prog, size)) { return 1; }\n";
}

bool contains(const std::string &haystack, const std::string &needle)
{
  return std::string::npos != haystack.find(needle);
}

bool handle_start(
  const goto_functionst &gf,
  std::string &source,
  const std::string &line)
{
  std::ostringstream start_sig;
  start_sig << "void " << gf.entry_point() << "(void)";
  if(start_sig.str()!=line)
    return false;
  source+="int main(const int argc, const char * const argv[])\n";
  return true;
}

bool handle_return_value(const std::string &line)
{
  return contains(line, "main#return_value") || contains(line, "_return'");
}

#define PROG_PREFIX "  struct " CEGIS_PREFIX "instructiont "
#define PROG_PREFIX_LEN strlen(PROG_PREFIX)

void replace_ce_index(std::string &line)
{
  substitute(line, "[" CEGIS_PREFIX "x_index]", "[0u]");
}

void replace_assume(std::string &line)
{
  substitute(line, "__CPROVER_assume", CEGIS_PREFIX "assert");
}

void replace_danger_execute_size(std::string &line)
{
  if (!contains(line, "__CPROVER_danger_execute(")) return;
  const std::string::size_type name_start=line.find('(') + 1;
  const std::string::size_type name_end=line.find(',');
  const std::string::size_type name_len=name_end - name_start;
  const std::string name(line.substr(name_start, name_len));
  line.erase(name_end, std::string::npos);
  line+=", ";
  line+=name;
  line+="_size);\n";
}

void replace_return_values(std::string &line)
{
  substitute(line, "OUTPUT(\"return\", return')", "");
  substitute(line, "#return_value", "__return_value");
  substitute(line, "return'", "__return_value");
}

void fix_cprover_names(std::string &line)
{
  substitute(line, "$$", "__");
}

bool handle_programs(std::string &source, bool &initialised,
    const std::string &line)
{
  const size_t len=PROG_PREFIX_LEN;
  if (PROG_PREFIX != line.substr(0, len)) return false;
  if (!initialised)
  {
    source+="  " CEGIS_PREFIX "deserialise_init();\n";
    initialised=true;
  }
  const std::string::size_type name_len=line.find('[', len) - len;
  std::string name(line.substr(len, name_len));
  fix_cprover_names(name);
  source+="  " CEGIS_PREFIX "declare_prog(";
  source+=name;
  source+=", ";
  source+=name;
  source+="_size";
  source+=");\n";
  return true;
}

bool handle_x0(std::string &source, std::string &line)
{
  if (!contains(line, "__CPROVER") || !contains(line, "_x0_")
      || contains(line, "=")) return false;
  fix_cprover_names(line);
  const std::string::size_type name_start=line.rfind(' ') + 1;
  const std::string name(line.substr(name_start, line.size() - name_start - 1));
  source+=line;
  source+="\n  " CEGIS_PREFIX "deserialise_x0(";
  source+=name;
  source+=");\n";
  return true;
}

bool handle_ce(std::string &source, bool &initialised, const std::string &line)
{
  if (!(contains(line, CEGIS_PREFIX "x_choice_")
      || contains(line, CEGIS_PREFIX "x0_choice_"))
      || contains(line, CEGIS_PREFIX "x_index")) return false;
  if (!initialised)
  {
    source+="  " CEGIS_PREFIX "ce_value_init();\n";
    initialised=true;
  }
  const std::string::size_type name_end=line.find("={ ");
  source+="\n";
  std::string prefix=line.substr(0, name_end);
  fix_cprover_names(prefix);
  source+=prefix;
  source+="={ " CEGIS_PREFIX "ce_value() };\n";
  return true;
}

bool handle_second_instr_struct(std::string &source, const std::string &line)
{
  if ("struct " CEGIS_PREFIX "instructiont" != line) return false;
  source+="struct " CEGIS_PREFIX "instructiont_escaped\n";
  return true;
}

bool handle_ce_loop(const std::string &line, std::stringstream &ss)
{
  if ("    " CEGIS_PREFIX "x_index = " CEGIS_PREFIX "x_index + 1u;" == line
      || "  do" == line)
  {
    std::string skip;
    std::getline(ss, skip);
    return true;
  }
  return "  while(" CEGIS_PREFIX "index < 2u);" == line;
}

bool handle_internals(const std::string &line)
{
  if (contains(line, "ARRAY_OF(")) return true;
  return contains(line, "__CPROVER_malloc_size =")
      || contains(line, "__CPROVER_dead_object =")
      || contains(line, "__CPROVER_deallocated =")
      || contains(line, "__CPROVER_malloc_is_new_array =")
      || contains(line, "__CPROVER_malloc_object =")
      || contains(line, "__CPROVER_malloc_size =")
      || contains(line, "__CPROVER_memory_leak =")
      || contains(line, "__CPROVER_next_thread_id =")
      || contains(line, "__CPROVER_pipe_count =")
      || contains(line, "__CPROVER_rounding_mode =")
      || contains(line, "__CPROVER_thread_id =")
      || contains(line, "__CPROVER_threads_exited =")
      || "  assert((_Bool)0);" == line || "void assert(void);" == line
      || "static signed int assert#return_value;" == line;
}

void post_process(
  const goto_functionst &gf,
  std::string &source,
  std::stringstream &ss)
{
  bool deserialise_initialised=false;
  bool ce_initialised=false;
  for (std::string line; std::getline(ss, line);)
  {
    if(handle_start(gf, source, line) ||
       handle_return_value(line) ||
       handle_ce_loop(line, ss) ||
       handle_internals(line) ||
       handle_programs(source, deserialise_initialised, line) ||
       handle_x0(source, line) ||
       handle_ce(source, ce_initialised, line) ||
       handle_second_instr_struct(source, line))
      continue;
    replace_ce_index(line);
    replace_assume(line);
    fix_cprover_names(line);
    replace_danger_execute_size(line);
    replace_return_values(line);
    source+=line;
    source+='\n';
  }
}

void add_first_prog_offset(std::string &source, const size_t num_ce_vars)
{
  source+="#define " CEGIS_PREFIX "first_prog_offset ";
  source+=integer2string(num_ce_vars);
  source+="\n";
}
}

std::string &post_process_fitness_source(std::string &result,
    const symbol_tablet &st, const goto_functionst &gf,
    const size_t num_ce_vars, const size_t num_vars, const size_t num_consts,
    const size_t max_prog_size, const std::string &exec)
{
  const bool danger=DANGER_EXECUTE == exec;
  implement_program_individual_deserialise(result, danger);
  const namespacet ns(st);
  std::stringstream ss;
  dump_c(gf, true, ns, ss);
  add_first_prog_offset(result, num_ce_vars);
  add_assume_implementation(result);
  add_danger_execute(result, num_vars, num_consts, max_prog_size, exec);
  post_process(gf, result, ss);
  transform_program_individual_main_to_lib(result, danger);
  return result;
}
