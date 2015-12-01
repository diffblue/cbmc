#include <cstdlib>
#include <fstream>

#ifndef _WIN32
#include <sys/wait.h>
#endif

#include <util/bv_arithmetic.h>
#include <util/mp_arith.h>

#include <cegis/genetic/concrete_test_runner.h>

#define EXECUTABLE_PREFIX "test_runner"
#define EXECUTABLE_SUFFIX ".exe"
#define SOURCE_FILE_PREFIX "concrete_test"
#define SOURCE_FILE_SUFFIX ".c"

concrete_test_runnert::concrete_test_runnert(
    const std::function<std::string(void)> source_code_provider) :
    source_code_provider(source_code_provider), executable(EXECUTABLE_PREFIX,
    EXECUTABLE_SUFFIX), executable_compiled(false)
{
}

concrete_test_runnert::~concrete_test_runnert()
{
}

namespace
{
void implement_deserialise(std::string &source)
{
  source+=
      "#include <stdlib.h>\n\n"
          "#define __CPROVER_cegis_next_arg() atol(argv[__CPROVER_cegis_deserialise_index++])\n"
          "#define __CPROVER_cegis_deserialise_init() unsigned int __CPROVER_cegis_deserialise_index=1u+__CPROVER_cegis_first_prog_offset\n"
          "#define __CPROVER_cegis_declare_prog(var_name, sz) const size_t sz=__CPROVER_cegis_next_arg(); \\\n"
          "  struct __CPROVER_danger_instructiont var_name[sz]; \\\n"
          "for (unsigned int i=0; i < sizeof(var_name) / sizeof(struct __CPROVER_danger_instructiont); ++i) \\\n"
          "{ \\\n"
          "  var_name[i].opcode=__CPROVER_cegis_next_arg(); \\\n"
          "  var_name[i].op0=__CPROVER_cegis_next_arg(); \\\n"
          "  var_name[i].op1=__CPROVER_cegis_next_arg(); \\\n"
          "  var_name[i].op2=__CPROVER_cegis_next_arg(); \\\n"
          "}\n"
          "#define __CPROVER_cegis_deserialise_x0(var_name) var_name=__CPROVER_cegis_next_arg()\n"
          "#define __CPROVER_cegis_ce_value_init() unsigned int __CPROVER_cegis_ce_index=1u\n"
          "#define __CPROVER_cegis_ce_value() atol(argv[__CPROVER_cegis_ce_index++])\n";

}

void write_file(const char * const path, const std::string &content)
{
  std::ofstream ofs(path);
  ofs << content;
}

#define COMPILE_COMMAND "gcc -std=c99 -g0 -O3 "
#define ARTIFACT_SEPARATOR " -o "
#define COMPLING_FAILED "Compiling test runner failed."

void prepare_executable(bool &executable_compiled,
    const std::function<std::string(void)> &source_code_provider,
    const std::string &executable)
{
  if (executable_compiled) return;
  const temporary_filet source_file(SOURCE_FILE_PREFIX, SOURCE_FILE_SUFFIX);
  const std::string source_file_name(source_file());
  std::string source;
  implement_deserialise(source);
  source+=source_code_provider();
  write_file(source_file_name.c_str(), source);
  std::string compile_command(COMPILE_COMMAND);
  compile_command+=source_file_name;
  compile_command+=ARTIFACT_SEPARATOR;
  compile_command+=executable;
  const int result=system(compile_command.c_str());
  if (result) throw std::runtime_error(COMPLING_FAILED);
  executable_compiled=true;
}

#ifdef _WIN32
#define NOT_SUPPORTED() assert(!"task_poolt not supported on Windows.")
#endif

class conrete_test_runner_taskt
{
  concrete_test_runnert::individualt &ind;
  const std::string command;
public:
  conrete_test_runner_taskt(concrete_test_runnert::individualt &ind,
      const std::string &command) :
      ind(ind), command(command)
  {
  }

  int operator()() const
  {
#ifndef _WIN32
    const int result=system(command.c_str());
    if (!WIFEXITED(result)) return EXIT_FAILURE;
    return WEXITSTATUS(result);
#else
    NOT_SUPPORTED();
#endif
  }

  void operator()(const int status) const
  {
#ifndef _WIN32
    if (!WIFEXITED(status)) return;
    if (EXIT_SUCCESS == WEXITSTATUS(status)) ++ind.fitness;
#else
    NOT_SUPPORTED();
#endif
  }
};

#define NUM_RUNNER_OPS 3u
}

void concrete_test_runnert::run_test(individualt &ind,
    const counterexamplet &ce)
{
  const std::string exe(executable());
  prepare_executable(executable_compiled, source_code_provider, exe);
  std::string command(exe);
  for (const std::pair<const irep_idt, exprt> &assignment : ce)
  {
    command+=" ";
    const bv_arithmetict arith(assignment.second);
    const mp_integer::llong_t v=arith.to_integer().to_long();
    command+=integer2string(static_cast<unsigned int>(v));
  }
  for (const individualt::programt &prog : ind.programs)
  {
    if (prog.empty()) continue;
    command+=" ";
    command+=integer2string(prog.size());
    for (const individualt::instructiont &instr : prog)
    {
      command+=" ";
      command+=integer2string(static_cast<unsigned int>(instr.opcode));
      size_t op_count=0;
      for (const individualt::instructiont::opt &op : instr.ops)
      {
        command+=" ";
        command+=integer2string(static_cast<unsigned int>(op));
        ++op_count;
      }
      for (; op_count < 3u; ++op_count)
        command+=" 0";
    }
  }
  for (const individualt::x0t::value_type &x0 : ind.x0)
  {
    command+=" ";
    command+=integer2string(static_cast<unsigned int>(x0));
  }
  const conrete_test_runner_taskt task(ind, command);
  task_pool.schedule(task, task);
}

void concrete_test_runnert::join()
{
  task_pool.join_all();
}
