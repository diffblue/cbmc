/*******************************************************************\

Module: LD Mode

Author: CM Wintersteiger, 2006

\*******************************************************************/

/// \file
/// LD Mode

#include "ld_mode.h"

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <algorithm>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <numeric>
#include <sstream>

#include <json/json_parser.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr.h>
#include <util/get_base_name.h>
#include <util/invariant.h>
#include <util/prefix.h>
#include <util/replace_symbol.h>
#include <util/run.h>
#include <util/suffix.h>
#include <util/tempdir.h>
#include <util/tempfile.h>

#include <goto-programs/read_goto_binary.h>

#include "hybrid_binary.h"
#include "linker_script_merge.h"

static std::string
linker_name(const cmdlinet &cmdline, const std::string &base_name)
{
  if(cmdline.isset("native-linker"))
    return cmdline.get_value("native-linker");

  std::string::size_type pos = base_name.find("goto-ld");

  if(
    pos == std::string::npos || base_name == "goto-gcc" ||
    base_name == "goto-ld")
    return "ld";

  std::string result = base_name;
  result.replace(pos, 7, "ld");

  return result;
}

ld_modet::ld_modet(goto_cc_cmdlinet &_cmdline, const std::string &_base_name)
  : goto_cc_modet(_cmdline, _base_name, gcc_message_handler),
    goto_binary_tmp_suffix(".goto-cc-saved")
{
}

/// does it.
int ld_modet::doit()
{
  if(cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  native_tool_name = linker_name(cmdline, base_name);

  if(cmdline.isset("version") || cmdline.isset("print-sysroot"))
    return run_ld();

  eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_ERROR, gcc_message_handler);

  compilet compiler(cmdline, gcc_message_handler, false);

  // determine actions to be undertaken
  compiler.mode = compilet::LINK_LIBRARY;

  // model validation
  compiler.validate_goto_model = cmdline.isset("validate-goto-model");

  // get configuration
  config.set(cmdline);

  compiler.object_file_extension = "o";

  if(cmdline.isset('L'))
    compiler.library_paths = cmdline.get_values('L');
  // Don't add the system paths!

  if(cmdline.isset('l'))
    compiler.libraries = cmdline.get_values('l');

  if(cmdline.isset("static"))
    compiler.libraries.push_back("c");

  if(cmdline.isset('o'))
  {
    // given gcc -o file1 -o file2,
    // gcc will output to file2, not file1
    compiler.output_file_object = cmdline.get_values('o').back();
    compiler.output_file_executable = cmdline.get_values('o').back();
  }
  else
  {
    compiler.output_file_object.clear();
    compiler.output_file_executable = "a.out";
  }

  // We now iterate over any input files

  for(const auto &arg : cmdline.parsed_argv)
    if(arg.is_infile_name)
      compiler.add_input_file(arg.arg);

  // Revert to gcc in case there is no source to compile
  // and no binary to link.

  if(compiler.source_files.empty() && compiler.object_files.empty())
    return run_ld(); // exit!

  // do all the rest
  if(compiler.doit())
    return 1; // LD exit code for all kinds of errors

  // We can generate hybrid ELF and Mach-O binaries
  // containing both executable machine code and the goto-binary.
  return ld_hybrid_binary(compiler);
}

int ld_modet::run_ld()
{
  PRECONDITION(!cmdline.parsed_argv.empty());

  // build new argv
  std::vector<std::string> new_argv;
  new_argv.reserve(cmdline.parsed_argv.size());
  for(const auto &a : cmdline.parsed_argv)
    new_argv.push_back(a.arg);

  // overwrite argv[0]
  new_argv[0] = native_tool_name;

  debug() << "RUN:";
  for(std::size_t i = 0; i < new_argv.size(); i++)
    debug() << " " << new_argv[i];
  debug() << eom;

  return run(new_argv[0], new_argv, cmdline.stdin_file, "", "");
}

int ld_modet::ld_hybrid_binary(compilet &compiler)
{
  std::string output_file;

  if(cmdline.isset('o'))
  {
    output_file = cmdline.get_value('o');

    if(output_file == "/dev/null")
      return EX_OK;
  }
  else
    output_file = "a.out";

  debug() << "Running " << native_tool_name << " to generate hybrid binary"
          << eom;

  // save the goto-cc output file
  std::string goto_binary = output_file + goto_binary_tmp_suffix;

  int result;

  result = rename(output_file.c_str(), goto_binary.c_str());
  if(result != 0)
  {
    error() << "Rename failed: " << std::strerror(errno) << eom;
    return result;
  }

  result = run_ld();

  if(result == 0 && cmdline.isset('T'))
  {
    linker_script_merget ls_merge(
      compiler, output_file, goto_binary, cmdline, get_message_handler());
    result = ls_merge.add_linker_script_definitions();
  }

  if(result == 0)
  {
    std::string native_linker = linker_name(cmdline, base_name);

    result = hybrid_binary(
      native_linker,
      goto_binary,
      output_file,
      compiler.mode == compilet::COMPILE_LINK_EXECUTABLE,
      get_message_handler());
  }

  return result;
}

/// display command line help
void ld_modet::help_mode()
{
  std::cout << "goto-ld understands the options of "
            << "ld plus the following.\n\n";
}
