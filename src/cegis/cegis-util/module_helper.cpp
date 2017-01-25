/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifdef _WIN32
#include <Windows.h>
#else
#include <limits.h>
#include <unistd.h>
#include <stdexcept>
#endif
#include <cegis/cegis-util/module_helper.h>

std::string get_current_executable_file_path()
{
#ifdef _WIN32
  char buffer[MAX_PATH];
  GetModuleFileName(NULL, buffer, MAX_PATH);
  return std::string(buffer);
#else
  char buffer[PATH_MAX];
  const ssize_t len=::readlink("/proc/self/exe", buffer, sizeof(buffer) - 1);
  if (len == -1) throw std::runtime_error("module helper: readlink failed");
  buffer[len]='\0';
  return std::string(buffer);
#endif
}
