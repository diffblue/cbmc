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

#include <cstring>
#include <fstream>
#include <iostream>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/file_util.h>
#include <util/invariant.h>
#include <util/run.h>

#include "compile.h"
#include "goto_cc_cmdline.h"
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

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_ERROR, gcc_message_handler);

  compilet compiler(
    cmdline,
    gcc_message_handler,
    cmdline.isset("fatal-warnings") && !cmdline.isset("no-fatal-warnings"));

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
  return ld_hybrid_binary(
    compiler.mode == compilet::COMPILE_LINK_EXECUTABLE, compiler.object_files);
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

  messaget log{gcc_message_handler};
  log.debug() << "RUN:";
  for(std::size_t i = 0; i < new_argv.size(); i++)
    log.debug() << " " << new_argv[i];
  log.debug() << messaget::eom;

  return run(new_argv[0], new_argv, cmdline.stdin_file, "", "");
}

int ld_modet::ld_hybrid_binary(
  bool building_executable,
  const std::list<std::string> &object_files)
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

  messaget log{gcc_message_handler};
  log.debug() << "Running " << native_tool_name << " to generate hybrid binary"
              << messaget::eom;

  // save the goto-cc output file
  std::string goto_binary = output_file + goto_binary_tmp_suffix;

  try
  {
    file_rename(output_file, goto_binary);
  }
  catch(const cprover_exception_baset &e)
  {
    log.error() << "Rename failed: " << e.what() << messaget::eom;
    return 1;
  }

  const bool linking_efi = cmdline.get_value('m') == "i386pep";

#ifdef __linux__
  if(linking_efi)
  {
    const std::string objcopy_cmd = objcopy_command(native_tool_name);

    for(const auto &object_file : object_files)
    {
      log.debug() << "stripping goto-cc sections before building EFI binary"
                  << messaget::eom;
      // create a backup copy
      const std::string bin_name = object_file + goto_binary_tmp_suffix;

      std::ifstream in(object_file, std::ios::binary);
      std::ofstream out(bin_name, std::ios::binary);
      out << in.rdbuf();

      // remove any existing goto-cc section
      std::vector<std::string> objcopy_argv;

      objcopy_argv.push_back(objcopy_cmd);
      objcopy_argv.push_back("--remove-section=goto-cc");
      objcopy_argv.push_back(object_file);

      if(run(objcopy_argv[0], objcopy_argv) != 0)
      {
        log.debug() << "EFI binary preparation: removing goto-cc section failed"
                    << messaget::eom;
      }
    }
  }
#else
  (void)object_files; // unused parameter
#endif

  int result = run_ld();

  if(result == 0 && cmdline.isset('T'))
  {
    linker_script_merget ls_merge(
      output_file, goto_binary, cmdline, message_handler);
    result = ls_merge.add_linker_script_definitions();
  }

#ifdef __linux__
  if(linking_efi)
  {
    log.debug() << "arch set with " << object_files.size() << messaget::eom;
    for(const auto &object_file : object_files)
    {
      log.debug() << "EFI binary preparation: restoring object files"
                  << messaget::eom;
      const std::string bin_name = object_file + goto_binary_tmp_suffix;
      const int mv_result = rename(bin_name.c_str(), object_file.c_str());
      if(mv_result != 0)
      {
        log.debug() << "Rename failed: " << std::strerror(errno)
                    << messaget::eom;
      }
    }
  }
#endif

  if(result == 0)
  {
    std::string native_linker = linker_name(cmdline, base_name);

    result = hybrid_binary(
      native_linker,
      goto_binary,
      output_file,
      building_executable,
      message_handler,
      linking_efi);
  }

  return result;
}

/// display command line help
void ld_modet::help_mode()
{
  std::cout << "goto-ld understands the options of "
            << "ld plus the following.\n\n";
}
