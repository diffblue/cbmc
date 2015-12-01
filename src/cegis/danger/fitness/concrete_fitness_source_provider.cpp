#include <cstring>

#include <util/expr_util.h>
#include <util/substitute.h>

#include <goto-instrument/dump_c.h>

#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/symex/learn/danger_library.h>
#include <cegis/danger/symex/verify/insert_constraint.h>
#include <cegis/danger/fitness/concrete_fitness_source_provider.h>

concrete_fitness_source_providert::concrete_fitness_source_providert(
    const danger_programt &prog, const std::function<size_t(void)> max_size) :
    prog(prog), max_size(max_size), learn_config(prog)
{
}

concrete_fitness_source_providert::~concrete_fitness_source_providert()
{
}

namespace
{
void add_assume_implementation(std::string &source)
{
  source+=
      "#define __CPROVER_cegis_assert(constraint) if(constraint) { return 0; } else { return 1; }\n";
  source+="#define __CPROVER_assume(constraint) \n";
  source+=
      "#define __CPROVER_danger_execute_assume(constraint) if (!(constraint)) { return 1; }\n";
}

void add_danger_execute(std::string &source, const size_t num_vars,
    const size_t num_consts, const size_t max_prog_size)
{
  std::string text=get_danger_library_text(num_vars, num_consts, max_prog_size);
  substitute(text, "#define opcode program[i].opcode",
      "const opcodet opcode=program[i].opcode;");
  substitute(text, "#line 1 \"<builtin-library>\"",
      "//#line 2 \"<builtin-library>\"");
  substitute(text, "#line 1 \"<builtin-library-__CPROVER_danger_execute>\"",
      "//#line 2 \"<builtin-library-__CPROVER_danger_execute>\"");
  const char result_op[]=
      "    *(unsigned int *)__CPROVER_danger_RESULT_OPS[i]=result;\n  }\n";
  const std::string::size_type pos=text.find(result_op);
  assert(std::string::npos != pos);
  text.insert(pos + strlen(result_op),
      "if (size <= 0 || size >= __CPROVER_danger_max_solution_size) return 0;\n"
          "int diff=__CPROVER_danger_max_solution_size-size;\n"
          "for (int i = size-1; i >= 0; --i) {\n"
          "  *(unsigned int *)__CPROVER_danger_RESULT_OPS[i+diff]=*(unsigned int *)__CPROVER_danger_RESULT_OPS[i];\n"
          "}\n"
          "return 0;\n");
  substitute(text, "__CPROVER_assume(op0_ptr && op1_ptr && op2_ptr)",
      "__CPROVER_danger_execute_assume(op0_ptr && op1_ptr && op2_ptr)");
  substitute(text, "__CPROVER_assume((opcode != 19 && opcode != 20) || op1)",
      "__CPROVER_danger_execute_assume(opcode != 19 && opcode != 20 || op1)");
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

bool handle_start(std::string &source, const std::string &line)
{
  if ("void _start(void)" != line) return false;
  source+="int main(const int argc, const char * const argv[])\n";
  return true;
}

bool handle_return_value(const std::string &line)
{
  return contains(line, "main#return_value");
}

#define PROG_PREFIX "  struct __CPROVER_danger_instructiont "
#define PROG_PREFIX_LEN strlen(PROG_PREFIX)

void replace_ce_index(std::string &line)
{
  substitute(line, "[__CPROVER_danger_x_index]", "[0u]");
}

void replace_assume(std::string &line)
{
  substitute(line, "__CPROVER_assume", "__CPROVER_cegis_assert");
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
  substitute(line, "#return_value", "__return_value");
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
    source+="  __CPROVER_cegis_deserialise_init();\n";
    initialised=true;
  }
  const std::string::size_type name_len=line.find('[', len) - len;
  std::string name(line.substr(len, name_len));
  fix_cprover_names(name);
  source+="  __CPROVER_cegis_declare_prog(";
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
  source+="\n  __CPROVER_cegis_deserialise_x0(";
  source+=name;
  source+=");\n";
  return true;
}

bool handle_ce(std::string &source, bool &initialised, const std::string &line)
{
  if (!contains(line, "__CPROVER_danger_x_choice_")
      || contains(line, "__CPROVER_danger_x_index")) return false;
  if (!initialised)
  {
    source+="  __CPROVER_cegis_ce_value_init();\n";
    initialised=true;
  }
  const std::string::size_type name_end=line.find(" = { ");
  source+="\n";
  std::string prefix=line.substr(0, name_end);
  fix_cprover_names(prefix);
  source+=prefix;
  source+=" = { __CPROVER_cegis_ce_value() };\n";
  return true;
}

bool handle_second_instr_struct(std::string &source, const std::string &line)
{
  if ("struct __CPROVER_danger_instructiont" != line) return false;
  source+="struct __CPROVER_danger_instructiont_escaped\n";
  return true;
}

bool handle_ce_loop(const std::string &line, std::stringstream &ss)
{
  if ("    __CPROVER_danger_x_index = __CPROVER_danger_x_index + 1u;" == line
      || "  do" == line)
  {
    std::string skip;
    std::getline(ss, skip);
    return true;
  }
  return "  while(__CPROVER_danger_x_index < 2u);" == line;
}

bool handle_internals(const std::string &line)
{
  if (contains(line, "ARRAY_OF(")) return true;
  return "    __CPROVER_malloc_size = 0u;" == line
      || "    __CPROVER_dead_object = NULL;" == line
      || "    __CPROVER_deallocated = NULL;" == line
      || "    __CPROVER_malloc_is_new_array = 0 != 0;" == line
      || "    __CPROVER_malloc_object = NULL;" == line
      || "    __CPROVER_malloc_size = 0ul;" == line
      || "    __CPROVER_memory_leak = NULL;" == line
      || "    __CPROVER_next_thread_id = (unsigned long int)0;" == line
      || "    __CPROVER_pipe_count = (unsigned int)0;" == line
      || "    __CPROVER_rounding_mode = 0;" == line
      || "    __CPROVER_thread_id = (unsigned long int)0;" == line
      || "    __CPROVER_threads_exited = ARRAY_OF((_Bool)0);" == line
      || "  assert((_Bool)0);" == line || "void assert(void);" == line
      || "static signed int assert#return_value;" == line;
}

std::string &post_process(std::string &source, std::stringstream &ss)
{
  bool deserialise_initialised=false;
  bool ce_initialised=false;
  for (std::string line; std::getline(ss, line);)
  {
    if (handle_start(source, line) || handle_return_value(line)
        || handle_ce_loop(line, ss) || handle_internals(line)
        || handle_programs(source, deserialise_initialised, line)
        || handle_x0(source, line) || handle_ce(source, ce_initialised, line)
        || handle_second_instr_struct(source, line)) continue;
    replace_ce_index(line);
    replace_assume(line);
    fix_cprover_names(line);
    replace_danger_execute_size(line);
    replace_return_values(line);
    source+=line;
    source+='\n';
  }
  return source;
}

void add_first_prog_offset(std::string &source, const size_t num_ce_vars)
{
  source+="#define __CPROVER_cegis_first_prog_offset ";
  source+=integer2string(num_ce_vars);
  source+="\n";
}
}

std::string concrete_fitness_source_providert::operator ()()
{
  if (!source.empty()) return source;
  constraint_varst ce_vars;
  get_danger_constraint_vars(ce_vars, prog);
  danger_learn_configt::counterexamplet dummy_ce;
  const typet type(danger_meta_type());  // XXX: Currently single data type
  const exprt zero(gen_zero(type));
  for (const symbol_exprt &var : ce_vars)
    dummy_ce.insert(std::make_pair(var.get_identifier(), zero));
  danger_learn_configt::counterexamplest empty(1, dummy_ce);
  const size_t max_prog_size=max_size();
  learn_config.process(empty, max_prog_size);
  const symbol_tablet &st(learn_config.get_symbol_table());
  const goto_functionst &gf=learn_config.get_goto_functions();
  const size_t num_vars=learn_config.get_num_vars();
  const size_t num_consts=learn_config.get_num_consts();
  const namespacet ns(st);
  std::stringstream ss;
  dump_c(gf, true, ns, ss);
  add_first_prog_offset(source, ce_vars.size());
  add_assume_implementation(source);
  add_danger_execute(source, num_vars, num_consts, max_prog_size);
  post_process(source, ss);
  return source;
}
