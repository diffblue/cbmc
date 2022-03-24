/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include "tempdir.h"

#include <filesystem>

// clang-format off
#ifndef _WIN32
#if defined(__FreeBSD_kernel__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
#include <unistd.h>
#endif

#include <cstdlib>
#include <cstring>
#include <vector>
#endif
// clang-format on

#include "exception_utils.h"

std::string get_temporary_directory(const std::string &name_template)
{
  std::string result;

#ifdef _WIN32
  (void)name_template; // unused parameter
  try
  {
    result = std::filesystem::temp_directory_path().string();
  }
  catch(const std::filesystem::filesystem_error &)
  {
    throw system_exceptiont("Failed to create temporary directory");
  }
#else
  std::string prefixed_name_template = "/tmp/";
  const char *TMPDIR_env = getenv("TMPDIR");
  if(TMPDIR_env != nullptr)
    prefixed_name_template = TMPDIR_env;
  if(*prefixed_name_template.rbegin() != '/')
    prefixed_name_template += '/';
  prefixed_name_template += name_template;

  std::vector<char> t(
    prefixed_name_template.begin(), prefixed_name_template.end());
  t.push_back('\0'); // add the zero
  const char *td = mkdtemp(t.data());
  if(!td)
    throw system_exceptiont("Failed to create temporary directory");

  errno = 0;
  char *wd = realpath(td, nullptr);

  if(wd == nullptr)
    throw system_exceptiont(
      std::string("realpath failed: ") + std::strerror(errno));

  result = std::string(wd);
  free(wd);
#endif

  return result;
}

temp_dirt::temp_dirt(const std::string &name_template)
{
  path=get_temporary_directory(name_template);
}

std::string temp_dirt::operator()(const std::string &file)
{
  return std::filesystem::path(path).append(file).string();
}

void temp_dirt::clear()
{
  std::filesystem::remove_all(path);
}

temp_dirt::~temp_dirt()
{
  clear();
}
