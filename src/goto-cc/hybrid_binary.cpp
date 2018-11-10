/*******************************************************************\

Module: Create hybrid binary with goto-binary section

Author: Michael Tautschnig, 2018

\*******************************************************************/

/// \file
/// Create hybrid binary with goto-binary section

#include "hybrid_binary.h"

#include <util/run.h>
#include <util/suffix.h>

#include <cstring>

int hybrid_binary(
  const std::string &compiler_or_linker,
  const std::string &goto_binary_file,
  const std::string &output_file,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  int result;

#if defined(__linux__) || defined(__FreeBSD_kernel__)
  std::string objcopy_cmd;

  if(has_suffix(compiler_or_linker, "-ld"))
  {
    objcopy_cmd = compiler_or_linker;
    objcopy_cmd.erase(objcopy_cmd.size() - 2);
    objcopy_cmd += "objcopy";
  }
  else
    objcopy_cmd = "objcopy";

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

    result = run(objcopy_argv[0], objcopy_argv);
  }

  // delete the goto binary
  int remove_result = remove(goto_binary_file.c_str());
  if(remove_result != 0)
  {
    message.error() << "Remove failed: " << std::strerror(errno)
                    << messaget::eom;
    if(result == 0)
      result = remove_result;
  }

#elif defined(__APPLE__)
  // Mac

  message.debug() << "merging " << output_file << " and " << goto_binary_file
                  << " using lipo"
                  << messaget::eom;

  {
    // Add goto-binary as hppa7100LC section.
    // This overwrites if there's already one.
    std::vector<std::string> lipo_argv = {
      "lipo", output_file, "-create", "-arch", "hppa7100LC", goto_binary_file,
      "-output", output_file };

    result = run(lipo_argv[0], lipo_argv);
  }

  // delete the goto binary
  int remove_result = remove(goto_binary_file.c_str());
  if(remove_result != 0)
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
  message.error() << "binary merging not implemented for this platform"
                  << messaget::eom;
  result = 1;
#endif

  return result;
}
