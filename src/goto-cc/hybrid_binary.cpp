/*******************************************************************\

Module: Create hybrid binary with goto-binary section

Author: Michael Tautschnig, 2018

\*******************************************************************/

/// \file
/// Create hybrid binary with goto-binary section

#include "hybrid_binary.h"

#include <util/file_util.h>
#include <util/message.h>
#include <util/run.h>
#include <util/suffix.h>

#include <cstring>

#if defined(__APPLE__)
#  include <sys/stat.h>
#endif

std::string objcopy_command(const std::string &compiler_or_linker)
{
  if(has_suffix(compiler_or_linker, "-ld"))
  {
    std::string objcopy_cmd = compiler_or_linker;
    objcopy_cmd.erase(objcopy_cmd.size() - 2);
    objcopy_cmd += "objcopy";

    return objcopy_cmd;
  }
  else
    return "objcopy";
}

int hybrid_binary(
  const std::string &compiler_or_linker,
  const std::string &goto_binary_file,
  const std::string &output_file,
  bool building_executable,
  message_handlert &message_handler,
  bool linking_efi)
{
  messaget message(message_handler);

  int result = 0;

#if defined(__linux__) || defined(__FreeBSD_kernel__) || defined(__OpenBSD__)
  // we can use objcopy for both object files and executables
  (void)building_executable;

  const std::string objcopy_cmd = objcopy_command(compiler_or_linker);

  // merge output from gcc or ld with goto-binary using objcopy

  message.debug() << "merging " << output_file << " and " << goto_binary_file
                  << " using " << objcopy_cmd
                  << messaget::eom;

  {
    // Now add goto-binary as goto-cc section.
    // Remove if it exists before, or otherwise adding fails.
    std::vector<std::string> objcopy_argv = {
      objcopy_cmd,
      "--remove-section", "goto-cc",
      "--add-section", "goto-cc=" + goto_binary_file, output_file};

    const int add_section_result = run(objcopy_argv[0], objcopy_argv);
    if(add_section_result != 0)
    {
      if(linking_efi)
        message.warning() << "cannot merge EFI binaries: goto-cc section lost"
                          << messaget::eom;
      else
        result = add_section_result;
    }
  }

  // delete the goto binary
  bool remove_result = file_remove(goto_binary_file);
  if(!remove_result)
  {
    message.error() << "Remove failed: " << std::strerror(errno)
                    << messaget::eom;
    if(result == 0)
      result = remove_result;
  }

#elif defined(__APPLE__)
  // Mac

  message.debug() << "merging " << output_file << " and " << goto_binary_file
                  << " using " << (building_executable ? "lipo" : "ld")
                  << messaget::eom;

  if(building_executable)
  {
    // Add goto-binary as hppa7100LC section.
    // This overwrites if there's already one.
    std::vector<std::string> lipo_argv = {
      "lipo", output_file, "-create", "-arch", "hppa7100LC", goto_binary_file,
      "-output", output_file };

    result = run(lipo_argv[0], lipo_argv);

    if(result == 0)
    {
      // lipo creates an output file, but it does not set execute permissions,
      // so the user is unable to directly execute the output file until its
      // chmod +x
      mode_t current_umask = umask(0);
      umask(current_umask);
      int chmod_result = chmod(
        output_file.c_str(), (S_IRWXU | S_IRWXG | S_IRWXO) & ~current_umask);
      if(chmod_result != 0)
      {
        message.error() << "Setting execute permissions failed: "
                        << std::strerror(errno) << messaget::eom;
        result = chmod_result;
      }
    }
  }
  else
  {
    // This fails if there's already one.
    std::vector<std::string> ld_argv = {"ld",
                                        "-r",
                                        "-sectcreate",
                                        "__TEXT",
                                        "goto-cc",
                                        goto_binary_file,
                                        output_file,
                                        "-o",
                                        output_file};

    result = run(ld_argv[0], ld_argv);
  }

  // delete the goto binary
  bool remove_result = file_remove(goto_binary_file);
  if(!remove_result)
  {
    message.error() << "Remove failed: " << std::strerror(errno)
                    << messaget::eom;
    if(result == 0)
      result = remove_result;
  }

#else
  // unused parameters
  (void)compiler_or_linker;
  (void)goto_binary_file;
  (void)output_file;
  (void)building_executable;
  message.error() << "binary merging not implemented for this platform"
                  << messaget::eom;
  result = 1;
#endif

  return result;
}
