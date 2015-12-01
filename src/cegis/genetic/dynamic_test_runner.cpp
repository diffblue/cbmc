//#include <dlfcn.h>

#include <cstdlib>
#include <fstream>

#include <util/bv_arithmetic.h>
#include <util/substitute.h>

#include <cegis/genetic/dynamic_test_runner.h>

#define LIBRARY_PREFIX "fitness_test"
#ifndef _WIN32
#define LIBRARY_SUFFIX ".so"
#else
#define LIBRARY_SUFFIX ".dll"
#endif

dynamic_test_runnert::dynamic_test_runnert(
    const std::function<std::string(void)> &source_code_provider,
    const std::function<size_t(size_t)> &max_prog_sz) :
    source_code_provider(source_code_provider), max_prog_sz(max_prog_sz), shared_library(
    LIBRARY_PREFIX,
    LIBRARY_SUFFIX), handle(0), fitness_tester(0)
{
}

dynamic_test_runnert::~dynamic_test_runnert()
{
  if (fitness_tester)
  {
    #if 0
    dlclose(handle);
    #endif
  }
}

namespace
{
void implement_deserialise(std::string &source)
{
  source+=
      "#include <string.h>\n\n"
          "#define __CPROVER_cegis_next_arg() argv[__CPROVER_cegis_deserialise_index++]\n"
          "#define __CPROVER_cegis_deserialise_init() unsigned int __CPROVER_cegis_deserialise_index=__CPROVER_cegis_first_prog_offset\n"
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
          "#define __CPROVER_cegis_ce_value_init() unsigned int __CPROVER_cegis_ce_index=0u\n"
          "#define __CPROVER_cegis_ce_value() argv[__CPROVER_cegis_ce_index++]\n";

}

void write_file(const char * const path, const std::string &content)
{
  std::ofstream ofs(path);
  ofs << content;
}

#define SOURCE_FILE_PREFIX "concrete_test"
#define SOURCE_FILE_SUFFIX ".c"
#ifndef _WIN32
#define COMPILE_COMMAND "gcc -std=c99 -g0 -O2 -shared -rdynamic -fPIC "
//#define COMPILE_COMMAND "gcc -std=c99 -g3 -O0 -shared -rdynamic -fPIC "
#else
#define COMPILE_COMMAND "gcc -std=c99 -g0 -O2 -shared "
#endif
#define ARTIFACT_SEPARATOR " -o "
#define FUNC "__CPROVER_cegis_test_fitness"
#define COMPLING_FAILED "Compiling test runner failed."
#define OPEN_LIB_FAILED "Opening fitness test library failed."
#define LOAD_FUNC_FAILED "Loading fitness test function failed."

void prepare_library(dynamic_test_runnert::lib_handlet &handle,
    dynamic_test_runnert::fitness_testert &fitness_tester,
    const std::function<std::string(void)> &source_code_provider,
    const temporary_filet &library_file)
{
  if (fitness_tester) return;
  const temporary_filet source_file(SOURCE_FILE_PREFIX, SOURCE_FILE_SUFFIX);
  const std::string source_file_name(source_file());
  std::string source;
  implement_deserialise(source);
  source+=source_code_provider();
  substitute(source, "int main(const int argc, const char * const argv[])\n"
      "{\n",
      "int " FUNC "(const unsigned int argv[])\n"
      "{\n"
      "memset(__CPROVER_danger_OPS, 0, sizeof(__CPROVER_danger_OPS));\n"
      "memset(__CPROVER_danger_RESULT_OPS, 0, sizeof(__CPROVER_danger_RESULT_OPS));\n");
  write_file(source_file_name.c_str(), source);
  std::string compile_command(COMPILE_COMMAND);
  compile_command+=source_file_name;
  compile_command+=ARTIFACT_SEPARATOR;
  const std::string library(library_file());
  compile_command+=library;
  const int result=system(compile_command.c_str());
  if (result) throw std::runtime_error(COMPLING_FAILED);
  #if 0
  handle=dlopen(library.c_str(), RTLD_NOW);
  if (!handle)
  {
    perror(OPEN_LIB_FAILED);
    throw std::runtime_error(OPEN_LIB_FAILED);
  }
  fitness_tester=(dynamic_test_runnert::fitness_testert) dlsym(handle, FUNC);
  char *error=0;
  if ((error=dlerror()))
  {
    perror(error);
    throw std::runtime_error(LOAD_FUNC_FAILED);
  }
  #endif
}
}

void dynamic_test_runnert::run_test(individualt &ind, const counterexamplet &ce,
    const std::function<void(bool)> on_complete)
{
  prepare_library(handle, fitness_tester, source_code_provider, shared_library);
  std::deque<unsigned int> args;
  for (const std::pair<const irep_idt, exprt> &assignment : ce)
  {
    const bv_arithmetict arith(assignment.second);
    const mp_integer::llong_t v=arith.to_integer().to_long();
    args.push_back(static_cast<unsigned int>(v));
  }
  const individualt::programst &progs=ind.programs;
  const size_t num_progs=progs.size();
  for (size_t i=0; i < num_progs; ++i)
  {
    if (max_prog_sz(i) == 0u) continue;
    const individualt::programt &prog=progs[i];
    assert(!prog.empty());
    args.push_back(static_cast<unsigned int>(prog.size()));
    for (const individualt::instructiont &instr : prog)
    {
      args.push_back(static_cast<unsigned int>(instr.opcode));
      size_t op_count=0;
      for (const individualt::instructiont::opt &op : instr.ops)
      {
        args.push_back(static_cast<unsigned int>(op));
        ++op_count;
      }
      for (; op_count < 3u; ++op_count)
        args.push_back(0u);
    }
  }
  for (const individualt::x0t::value_type &x0 : ind.x0)
    args.push_back(static_cast<unsigned int>(x0));

  const int argc=args.size();
  unsigned int argv[argc];
  for (int i=0; i < argc; ++i)
    argv[i]=args[i];

  on_complete(EXIT_SUCCESS == fitness_tester(argv));
}

void dynamic_test_runnert::join()
{
}
