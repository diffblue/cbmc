/*******************************************************************\

Module:

Author: Daniel Kroening

Date: August 2012

\*******************************************************************/

#include "run.h"

#ifdef _WIN32
// clang-format off
#include <util/pragma_push.def>
#ifdef _MSC_VER
#pragma warning(disable:4668)
  // using #if/#elif on undefined macro
#endif
#include <process.h>
#include <windows.h>
#include <util/pragma_pop.def>
// clang-format on
#else

#include <cstring>
#include <cerrno>
#include <cstdio>
#include <cstdlib>

#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#endif

#include <fstream>

#include "invariant.h"
#include "signal_catcher.h"
#include "tempfile.h"
#include "unicode.h"

int run(const std::string &what, const std::vector<std::string> &argv)
{
  return run(what, argv, "", "", "");
}

#ifdef _WIN32
#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2
using fdt = HANDLE;
#else
using fdt = int;
#endif

/// open given file to replace either stdin, stderr, stdout
static fdt stdio_redirection(int fd, const std::string &file)
{
#ifdef _WIN32
  fdt result_fd = INVALID_HANDLE_VALUE;
  std::string name;

  SECURITY_ATTRIBUTES SecurityAttributes;
  ZeroMemory(&SecurityAttributes, sizeof SecurityAttributes);
  SecurityAttributes.bInheritHandle = true;

  switch(fd)
  {
  case STDIN_FILENO:
    name = "stdin";
    if(file.empty())
      result_fd = GetStdHandle(STD_INPUT_HANDLE);
    else
      result_fd = CreateFileW(
        widen(file).c_str(),
        GENERIC_READ,
        0,
        &SecurityAttributes,
        OPEN_EXISTING,
        FILE_ATTRIBUTE_READONLY,
        NULL);
    break;

  case STDOUT_FILENO:
    name = "stdout";
    if(file.empty())
      result_fd = GetStdHandle(STD_OUTPUT_HANDLE);
    else
      result_fd = CreateFileW(
        widen(file).c_str(),
        GENERIC_WRITE,
        0,
        &SecurityAttributes,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL);
    break;

  case STDERR_FILENO:
    name = "stderr";
    if(file.empty())
      result_fd = GetStdHandle(STD_ERROR_HANDLE);
    else
      result_fd = CreateFileW(
        widen(file).c_str(),
        GENERIC_WRITE,
        0,
        &SecurityAttributes,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL);
    break;

  default:
    UNREACHABLE;
  }

  if(result_fd == INVALID_HANDLE_VALUE)
    perror(("Failed to open " + name + " file " + file).c_str());

#else

  if(file.empty())
    return fd;

  int flags = 0, mode = 0;
  std::string name;

  switch(fd)
  {
  case STDIN_FILENO:
    flags = O_RDONLY;
    name = "stdin";
    break;

  case STDOUT_FILENO:
  case STDERR_FILENO:
    flags = O_CREAT | O_WRONLY;
    mode = S_IRUSR | S_IWUSR;
    name = fd == STDOUT_FILENO ? "stdout" : "stderr";
    break;

  default:
    UNREACHABLE;
  }

  const fdt result_fd = open(file.c_str(), flags, mode);

  if(result_fd == -1)
    perror(("Failed to open " + name + " file " + file).c_str());
#endif

  return result_fd;
}

#ifdef _WIN32
// Read
// https://blogs.msdn.microsoft.com/twistylittlepassagesallalike/2011/04/23/everyone-quotes-command-line-arguments-the-wrong-way/
std::wstring quote_windows_arg(const std::wstring &src)
{
  if(src.find_first_of(L" \t\n\v\"") == src.npos)
    return src;

  std::wstring result = L"\"";

  for(auto it = src.begin();; ++it)
  {
    std::size_t NumberBackslashes = 0;

    while(it != src.end() && *it == L'\\')
    {
      ++it;
      ++NumberBackslashes;
    }

    if(it == src.end())
    {
      //
      // Escape all backslashes, but let the terminating
      // double quotation mark we add below be interpreted
      // as a metacharacter.
      //

      result.append(NumberBackslashes * 2, L'\\');
      break;
    }
    else if(*it == L'"')
    {
      //
      // Escape all backslashes and the following
      // double quotation mark.
      //

      result.append(NumberBackslashes * 2 + 1, L'\\');
      result.push_back(*it);
    }
    else
    {
      //
      // Backslashes aren't special here.
      //

      result.append(NumberBackslashes, L'\\');
      result.push_back(*it);
    }
  }

  result.push_back(L'"');

  return result;
}
#endif

int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output,
  const std::string &std_error)
{
#ifdef _WIN32
  // unicode commandline, quoted
  std::wstring cmdline;

  // we replace argv[0] by what
  cmdline = quote_windows_arg(widen(what));

  for(std::size_t i = 1; i < argv.size(); i++)
  {
    cmdline += L" ";
    cmdline += quote_windows_arg(widen(argv[i]));
  }

  PROCESS_INFORMATION piProcInfo;
  STARTUPINFOW siStartInfo;

  ZeroMemory(&piProcInfo, sizeof piProcInfo);
  ZeroMemory(&siStartInfo, sizeof siStartInfo);

  siStartInfo.cb = sizeof siStartInfo;

  siStartInfo.hStdInput = stdio_redirection(STDIN_FILENO, std_input);
  siStartInfo.hStdOutput = stdio_redirection(STDOUT_FILENO, std_output);
  siStartInfo.hStdError = stdio_redirection(STDERR_FILENO, std_error);

  siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

  // CreateProcessW wants to modify the command line
  std::vector<wchar_t> mutable_cmdline(cmdline.begin(), cmdline.end());
  mutable_cmdline.push_back(0); // zero termination
  wchar_t *cmdline_ptr = mutable_cmdline.data();

  BOOL bSuccess = CreateProcessW(
    NULL,         // application name
    cmdline_ptr,  // command line
    NULL,         // process security attributes
    NULL,         // primary thread security attributes
    true,         // handles are inherited
    0,            // creation flags
    NULL,         // use parent's environment
    NULL,         // use parent's current directory
    &siStartInfo, // STARTUPINFO
    &piProcInfo); // PROCESS_INFORMATION

  if(!bSuccess)
  {
    if(!std_input.empty())
      CloseHandle(siStartInfo.hStdInput);
    if(!std_output.empty())
      CloseHandle(siStartInfo.hStdOutput);
    if(!std_error.empty())
      CloseHandle(siStartInfo.hStdError);
    return -1;
  }

  // wait for child to finish
  WaitForSingleObject(piProcInfo.hProcess, INFINITE);

  if(!std_input.empty())
    CloseHandle(siStartInfo.hStdInput);
  if(!std_output.empty())
    CloseHandle(siStartInfo.hStdOutput);
  if(!std_error.empty())
    CloseHandle(siStartInfo.hStdError);

  DWORD exit_code;

  // get exit code
  if(!GetExitCodeProcess(piProcInfo.hProcess, &exit_code))
  {
    CloseHandle(piProcInfo.hProcess);
    CloseHandle(piProcInfo.hThread);
    return -1;
  }

  CloseHandle(piProcInfo.hProcess);
  CloseHandle(piProcInfo.hThread);

  return exit_code;

#else
  int stdin_fd = stdio_redirection(STDIN_FILENO, std_input);
  int stdout_fd = stdio_redirection(STDOUT_FILENO, std_output);
  int stderr_fd = stdio_redirection(STDERR_FILENO, std_error);

  if(stdin_fd == -1 || stdout_fd == -1 || stderr_fd == -1)
    return 1;

  // temporarily suspend all signals
  sigset_t new_mask, old_mask;
  sigemptyset(&new_mask);
  sigprocmask(SIG_SETMASK, &new_mask, &old_mask);

  /* now create new process */
  pid_t childpid = fork();

  if(childpid>=0) /* fork succeeded */
  {
    if(childpid==0) /* fork() returns 0 to the child process */
    {
      // resume signals
      remove_signal_catcher();
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      std::vector<char *> _argv(argv.size()+1);
      for(std::size_t i=0; i<argv.size(); i++)
        _argv[i]=strdup(argv[i].c_str());

      _argv[argv.size()]=nullptr;

      if(stdin_fd!=STDIN_FILENO)
        dup2(stdin_fd, STDIN_FILENO);
      if(stdout_fd!=STDOUT_FILENO)
        dup2(stdout_fd, STDOUT_FILENO);
      if(stderr_fd != STDERR_FILENO)
        dup2(stderr_fd, STDERR_FILENO);

      errno=0;
      execvp(what.c_str(), _argv.data());

      /* usually no return */
      perror(std::string("execvp "+what+" failed").c_str());
      exit(1);
    }
    else /* fork() returns new pid to the parent process */
    {
      // must do before resuming signals to avoid race
      register_child(childpid);

      // resume signals
      sigprocmask(SIG_SETMASK, &old_mask, nullptr);

      int status;     /* parent process: child's exit status */

      /* wait for child to exit, and store its status */
      while(waitpid(childpid, &status, 0)==-1)
      {
        if(errno==EINTR)
          continue; // try again
        else
        {
          unregister_child();

          perror("Waiting for child process failed");
          if(stdin_fd!=STDIN_FILENO)
            close(stdin_fd);
          if(stdout_fd!=STDOUT_FILENO)
            close(stdout_fd);
          if(stderr_fd != STDERR_FILENO)
            close(stderr_fd);
          return 1;
        }
      }

      unregister_child();

      if(stdin_fd!=STDIN_FILENO)
        close(stdin_fd);
      if(stdout_fd!=STDOUT_FILENO)
        close(stdout_fd);
      if(stderr_fd != STDERR_FILENO)
        close(stderr_fd);

      return WEXITSTATUS(status);
    }
  }
  else /* fork returns -1 on failure */
  {
    // resume signals
    sigprocmask(SIG_SETMASK, &old_mask, nullptr);

    if(stdin_fd!=STDIN_FILENO)
      close(stdin_fd);
    if(stdout_fd!=STDOUT_FILENO)
      close(stdout_fd);
    if(stderr_fd != STDERR_FILENO)
      close(stderr_fd);

    return 1;
  }
#endif
}

/// quote a string for bash and CMD
static std::string shell_quote(const std::string &src)
{
  #ifdef _WIN32
  // first check if quoting is needed at all

  if(src.find(' ')==std::string::npos &&
     src.find('"')==std::string::npos &&
     src.find('&')==std::string::npos &&
     src.find('|')==std::string::npos &&
     src.find('(')==std::string::npos &&
     src.find(')')==std::string::npos &&
     src.find('<')==std::string::npos &&
     src.find('>')==std::string::npos &&
     src.find('^')==std::string::npos)
  {
    // seems fine -- return as is
    return src;
  }

  std::string result;

  result+='"';

  for(const char ch : src)
  {
    if(ch=='"')
      result+='"'; // quotes are doubled
    result+=ch;
  }

  result+='"';

  return result;

  #else

  // first check if quoting is needed at all

  if(src.find(' ')==std::string::npos &&
     src.find('"')==std::string::npos &&
     src.find('*')==std::string::npos &&
     src.find('$')==std::string::npos &&
     src.find('\\')==std::string::npos &&
     src.find('?')==std::string::npos &&
     src.find('&')==std::string::npos &&
     src.find('|')==std::string::npos &&
     src.find('>')==std::string::npos &&
     src.find('<')==std::string::npos &&
     src.find('^')==std::string::npos &&
     src.find('\'')==std::string::npos)
  {
    // seems fine -- return as is
    return src;
  }

  std::string result;

  // the single quotes catch everything but themselves!
  result+='\'';

  for(const char ch : src)
  {
    if(ch=='\'')
      result+="'\\''";
    result+=ch;
  }

  result+='\'';

  return result;
  #endif
}

int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  std::ostream &std_output,
  const std::string &std_error)
{
  #ifdef _WIN32
  temporary_filet tmpi("tmp.stdout", "");

  int result = run(what, argv, std_input, tmpi(), std_error);

  std::ifstream instream(tmpi());

  if(instream)
    std_output << instream.rdbuf(); // copy

  return result;
  #else
  std::string command;

  bool first = true;

  // note we use 'what' instead of 'argv[0]' as the name of the executable
  for(const auto &arg : argv)
  {
    if(first) // this is argv[0]
    {
      command += shell_quote(what);
      first = false;
    }
    else
      command += " " + shell_quote(arg);
  }

  if(!std_input.empty())
    command += " < " + shell_quote(std_input);

  if(!std_error.empty())
    command += " 2> " + shell_quote(std_error);

  FILE *stream=popen(command.c_str(), "r");

  if(stream!=nullptr)
  {
    int ch;
    while((ch=fgetc(stream))!=EOF)
      std_output << (unsigned char)ch;

    return pclose(stream);
  }
  else
    return -1;
  #endif
}
