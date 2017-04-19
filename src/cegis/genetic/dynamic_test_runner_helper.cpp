/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#if !defined(_WIN32) || defined(_HAVE_DLFCN)
#include <dlfcn.h>
#endif

#include <cassert>
#include <cstdlib>
#include <fstream>

#include <util/config.h>
#include <util/tempfile.h>

#include <cegis/instrument/literals.h>
#include <cegis/genetic/dynamic_test_runner_helper.h>

void close_fitness_tester_library(fitness_lib_handlet &handle)
{
  if(handle)
  {
#if !defined(_WIN32) || defined(_HAVE_DLFCN)
    dlclose(handle);
    handle=0;
#endif
  }
}

namespace
{
void write_file(const std::string &path, const std::string &content)
{
  std::ofstream ofs(path);
  ofs << content;
}

#define SOURCE_FILE_PREFIX "concrete_test"
#define SOURCE_FILE_SUFFIX ".c"
#ifndef _WIN32
#define COMPILE_COMMAND "gcc -std=c99 -g0 -O2 -shared -rdynamic -fPIC "
#define CLANG_COMPILE_COMMAND "clang -std=c99 -g0 -O2 -shared -rdynamic -fPIC "
#else
#define COMPILE_COMMAND "gcc -std=c99 -g0 -O2 -shared "
#define CLANG_COMPILE_COMMAND "clang -std=c99 -g0 -O2 "
#endif
#define ARTIFACT_SEPARATOR " -o "
#define COMPLING_FAILED "Compiling test runner failed."
#define OPEN_LIB_FAILED "Opening fitness test library failed."
#define LOAD_FUNC_FAILED "Loading fitness test function failed."
}

void *prepare_fitness_tester_library(fitness_lib_handlet &handle,
    const std::function<std::string(void)> &source_code_provider,
    const std::string &library_file_path, const std::string &compile_options)
{
  const temporary_filet source_file(SOURCE_FILE_PREFIX, SOURCE_FILE_SUFFIX);
  const std::string source_file_name(source_file());
  write_file(source_file_name, source_code_provider());
  std::string compile_command;
  if(configt::ansi_ct::preprocessort::CLANG == config.ansi_c.preprocessor)
    compile_command+=CLANG_COMPILE_COMMAND;
  else
    compile_command+=COMPILE_COMMAND;
  compile_command+=compile_options;
  compile_command+=source_file_name;
  compile_command+=ARTIFACT_SEPARATOR;
  compile_command+=library_file_path;
  const int result=system(compile_command.c_str());
  if(result) throw std::runtime_error(COMPLING_FAILED);

#if !defined(_WIN32) || defined(_HAVE_DLFCN)
  handle=dlopen(library_file_path.c_str(), RTLD_NOW);
  if(!handle)
  {
    perror(OPEN_LIB_FAILED);
    throw std::runtime_error(OPEN_LIB_FAILED);
  }
  void * const func_result=dlsym(handle, CEGIS_FITNESS_TEST_FUNC);
  char *error=0;
  if((error=dlerror()))
  {
    perror(error);
    throw std::runtime_error(LOAD_FUNC_FAILED);
  }
  return func_result;
#else
  assert(!"Dynamic library loading currently not supported on Windows.");
#endif
}
