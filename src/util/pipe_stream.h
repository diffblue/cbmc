/*******************************************************************\

Module: A stdin/stdout pipe as STL stream

Author:

\*******************************************************************/

#ifndef CPROVER_UTIL_PIPE_STREAM
#define CPROVER_UTIL_PIPE_STREAM

#include <iosfwd>
#include <string>
#include <list>

#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#include <sys/types.h>
#endif

// a class much like __gnu_cxx::stdio_filebuf

class filedescriptor_streambuf:public std::streambuf
{
public:
  #ifndef _WIN32
  typedef int HANDLE;
  #endif

  filedescriptor_streambuf();
  
  // these are closed automatically on destruction
  void set_in(HANDLE in) { proc_in=in; }
  void set_out(HANDLE out) { proc_out=out; }

  ~filedescriptor_streambuf();
  
protected:
  HANDLE proc_in, proc_out;
  char *in_buffer;

  int_type overflow(int_type);
  std::streamsize xsputn(const char *, std::streamsize);
  int_type underflow();
  std::streamsize xsgetn(char *, std::streamsize);
  std::streamsize showmanyc();
};

class pipe_stream:public std::iostream
{
public:
  pipe_stream(
    const std::string &_executable,
    const std::list<std::string> &_args);

  int run();
  int wait();

protected:
  std::string executable;
  std::list<std::string> args;

  #ifdef _WIN32
  PROCESS_INFORMATION pi;
  #else
  pid_t pid;
  #endif

  filedescriptor_streambuf buffer;
};

#endif
