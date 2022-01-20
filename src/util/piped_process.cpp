/// \file piped_process.cpp
/// Subprocess communication with pipes.
/// \author Diffblue Ltd.

// NOTES ON WINDOWS PIPES IMPLEMENTATION
//
// This is a note to explain the choices related to the Windows pipes
// implementation and to serve as information for future work on the
// Windows parts of this class.
//
// Windows supports two kinds of pipes: anonymous and named.
//
// Anonymous pipes can only operate in blocking mode. This is a problem for
// this class because blocking mode pipes (on Windows) will not allow the
// other end to read until the process providing the data has terminated.
// (You might think that this is not necessary, but in practice this is
// the case.) For example, if we ran
//    echo The Jabberwocky; ping 127.0.0.1 -n 6 >nul
// on the command line in Windows we would see the string "The Jabberwocky"
// immediately, and then the command would end about 6 seconds later after the
// pings complete. However, a blocking pipe will see nothing until the ping
// command has finished, even if the echo has completed and (supposedly)
// written to the pipe.
//
// For the above reason, we NEED to be able to use non-blocking pipes. Since
// anonymous pipes cannot be non-blocking (in theory they have a named pipe
// underneath, but it's not clear you could hack this to be non-blocking
// safely), we have to use named pipes.
//
// Named pipes can be non-blocking and this is how we create them.
//
// Aside on security:
// Named pipes can be connected to by other processes and here we have NOT
// gone deep into the security handling. The default used here is to allow
// access from the same session token/permissions. This SHOULD be sufficient
// for what we need.
//
// Non-blocking pipes allow immediate reading of any data on the pipe which
// matches the Linux/MacOS pipe behaviour and also allows reading of the
// string "The Jabberwocky" from the example above before waiting for the ping
// command to terminate. This reading can be done with any of the usual pipe
// read/peek functions, so we use those.
//
// There is one problem with the approach used here, that there is no Windows
// function that can wait on a non-blocking pipe. There are a few options that
// appear like they would work (or claim they work). Details on these and why
// they don't work are over-viewed here:
// -  WaitCommEvent claims it can wait for events on a handle (e.g. char
//    written) which would be perfect. Unfortunately on a non-blocking pipe
//    this returns immediately. Using this on a blocking pipe fails to detect
//    that a character is written until the other process terminates in the
//    example above, making this ineffective for what we want.
// -  Setting the pipe timeout or changing blocking after creation. This is
//    theoretically possible, but in practice either has no effect, or can
//    cause a segmentation fault. This was attempted with the SetCommTimeouts
//    function and cause segfault.
// -  Using a wait for event function (e.g. WaitForMultipleObjects, also single
//    object, event, etc.). These can in theory wait until an event, but have
//    the problem that with non-blocking pipes, the wait will not happen since
//    they return immediately. One might think they can work with a blocking
//    pipe and a timeout (i.e. have a blocking read and a timeout thread and
//    wait for one of them to happen to see if there is something to read or
//    whether we could timeout). However, while this can create the right
//    wait and timeout behaviour, since the underlying pipe is blocking this
//    means the example above cannot read "The Jabberwocky" until the ping has
//    finished, again undoing the interactive behaviour desired.
// Since none of the above work effectivley, the chosen approach is to use a
// non-blocking peek to see if there is anthing to read, and use a sleep and
// poll behaviour that might be much busier than we want. At the time of
// writing this has not been made smart, just a first choice option for how
// frequently to poll.
//
// Conclusion
// The implementation is written this way to mitigate the problems with what
// can and cannot be done with Windows pipes. It's not always pretty, but it
// does work and handles what we want.

#ifdef _WIN32
#  include "run.h"     // for Windows arg quoting
#  include "unicode.h" // for widen function
#  include <tchar.h>   // library for _tcscpy function
#  include <util/make_unique.h>
#  include <windows.h>
#else
#  include <fcntl.h>  // library for fcntl function
#  include <poll.h>   // library for poll function
#  include <signal.h> // library for kill function
#  include <unistd.h> // library for read/write/sleep/etc. functions
#endif

#  include <cstring> // library for strerror function (on linux)
#  include <iostream>
#  include <vector>

#  include "exception_utils.h"
#  include "invariant.h"
#  include "narrow.h"
#  include "optional.h"
#  include "piped_process.h"
#  include "string_utils.h"

#  define BUFSIZE 2048

#ifdef _WIN32
/// This function prepares a single wide string for the windows command
/// line.
/// \param commandvec: A vector of strings that contain the command and
///                    arguments to the command.
/// \returns A single wide string of the command appropriate for windows
static std::wstring
prepare_windows_command_line(const std::vector<std::string> &commandvec)
{
  std::wstring result = widen(commandvec[0]);
  for(int i = 1; i < commandvec.size(); i++)
  {
    result.append(L" ");
    result.append(quote_windows_arg(widen(commandvec[i])));
  }
  return result;
}
#endif

piped_processt::piped_processt(const std::vector<std::string> &commandvec)
{
#  ifdef _WIN32
  // Security attributes for pipe creation
  SECURITY_ATTRIBUTES sec_attr;
  sec_attr.nLength = sizeof(SECURITY_ATTRIBUTES);
  // Ensure pipes are inherited
  sec_attr.bInheritHandle = TRUE;
  // This sets the security to the default for the current session access token
  // See following link for details
  // https://docs.microsoft.com/en-us/previous-versions/windows/desktop/legacy/aa379560(v=vs.85) //NOLINT
  sec_attr.lpSecurityDescriptor = NULL;
  // Use named pipes to allow non-blocking read
  // Build the base name for the pipes
  std::string base_name = "\\\\.\\pipe\\cbmc\\child\\";
  // Use process ID as a unique ID for this process at this time.
  base_name.append(std::to_string(GetCurrentProcessId()));
  const std::string in_name = base_name + "\\IN";
  child_std_IN_Rd = CreateNamedPipe(
    in_name.c_str(),
    PIPE_ACCESS_INBOUND,          // Reading for us
    PIPE_TYPE_BYTE | PIPE_NOWAIT, // Bytes and non-blocking
    PIPE_UNLIMITED_INSTANCES,     // Probably doesn't matter
    BUFSIZE,
    BUFSIZE, // Output and input bufffer sizes
    0,       // Timeout in ms, 0 = use system default
    // This is the timeout that WaitNamedPipe functions will wait to try
    // and connect before aborting if no instance of the pipe is available.
    // In practice this is not used since we connect immediately and only
    // use one instance (no waiting for a free instance).
    &sec_attr); // For inheritance by child
  if(child_std_IN_Rd == INVALID_HANDLE_VALUE)
  {
    throw system_exceptiont("Input pipe creation failed for child_std_IN_Rd");
  }
  // Connect to the other side of the pipe
  child_std_IN_Wr = CreateFileA(
    in_name.c_str(),
    GENERIC_WRITE,                                  // Write side
    FILE_SHARE_READ | FILE_SHARE_WRITE,             // Shared read/write
    &sec_attr,                                      // Need this for inherit
    OPEN_EXISTING,                                  // Opening other end
    FILE_ATTRIBUTE_NORMAL | FILE_FLAG_NO_BUFFERING, // Normal, but don't buffer
    NULL);
  if(child_std_IN_Wr == INVALID_HANDLE_VALUE)
  {
    throw system_exceptiont("Input pipe creation failed for child_std_IN_Wr");
  }
  if(!SetHandleInformation(child_std_IN_Rd, HANDLE_FLAG_INHERIT, 0))
  {
    throw system_exceptiont(
      "Input pipe creation failed on SetHandleInformation");
  }
  const std::string out_name = base_name + "\\OUT";
  child_std_OUT_Rd = CreateNamedPipe(
    out_name.c_str(),
    PIPE_ACCESS_INBOUND,          // Reading for us
    PIPE_TYPE_BYTE | PIPE_NOWAIT, // Bytes and non-blocking
    PIPE_UNLIMITED_INSTANCES,     // Probably doesn't matter
    BUFSIZE,
    BUFSIZE,    // Output and input bufffer sizes
    0,          // Timeout in ms, 0 = use system default
    &sec_attr); // For inheritance by child
  if(child_std_OUT_Rd == INVALID_HANDLE_VALUE)
  {
    throw system_exceptiont("Output pipe creation failed for child_std_OUT_Rd");
  }
  child_std_OUT_Wr = CreateFileA(
    out_name.c_str(),
    GENERIC_WRITE,                                  // Write side
    FILE_SHARE_READ | FILE_SHARE_WRITE,             // Shared read/write
    &sec_attr,                                      // Need this for inherit
    OPEN_EXISTING,                                  // Opening other end
    FILE_ATTRIBUTE_NORMAL | FILE_FLAG_NO_BUFFERING, // Normal, but don't buffer
    NULL);
  if(child_std_OUT_Wr == INVALID_HANDLE_VALUE)
  {
    throw system_exceptiont("Output pipe creation failed for child_std_OUT_Wr");
  }
  if(!SetHandleInformation(child_std_OUT_Rd, HANDLE_FLAG_INHERIT, 0))
  {
    throw system_exceptiont(
      "Output pipe creation failed on SetHandleInformation");
  }
  // Create the child process
  STARTUPINFOW start_info;
  proc_info = util_make_unique<PROCESS_INFORMATION>();
  ZeroMemory(proc_info.get(), sizeof(PROCESS_INFORMATION));
  ZeroMemory(&start_info, sizeof(STARTUPINFOW));
  start_info.cb = sizeof(STARTUPINFOW);
  start_info.hStdError = child_std_OUT_Wr;
  start_info.hStdOutput = child_std_OUT_Wr;
  start_info.hStdInput = child_std_IN_Rd;
  start_info.dwFlags |= STARTF_USESTDHANDLES;
  const std::wstring cmdline = prepare_windows_command_line(commandvec);
  // Note that we do NOT free this since it becomes part of the child
  // and causes heap corruption in Windows if we free!
  const BOOL success = CreateProcessW(
    NULL,                     // application name, we only use the command below
    _wcsdup(cmdline.c_str()), // command line
    NULL,                     // process security attributes
    NULL,                     // primary thread security attributes
    TRUE,                     // handles are inherited
    0,                        // creation flags
    NULL,                     // use parent's environment
    NULL,                     // use parent's current directory
    &start_info,              // STARTUPINFO pointer
    proc_info.get());         // receives PROCESS_INFORMATION
  // Close handles to the stdin and stdout pipes no longer needed by the
  // child process. If they are not explicitly closed, there is no way to
  // recognize that the child process has ended (but maybe we don't care).
  CloseHandle(child_std_OUT_Wr);
  CloseHandle(child_std_IN_Rd);
#  else

  if(pipe(pipe_input) == -1)
  {
    throw system_exceptiont("Input pipe creation failed");
  }

  if(pipe(pipe_output) == -1)
  {
    throw system_exceptiont("Output pipe creation failed");
  }


  if(fcntl(pipe_output[0], F_SETFL, O_NONBLOCK) < 0)
  {
    throw system_exceptiont("Setting pipe non-blocking failed");
  }

  // Create a new process for the child that will execute the
  // command and receive information via pipes.
  child_process_id = fork();
  if(child_process_id == 0)
  {
    // child process here

    // Close pipes that will be used by the parent so we do
    // not have our own copies and conflicts.
    close(pipe_input[1]);
    close(pipe_output[0]);

    // Duplicate pipes so we have the ones we need.
    dup2(pipe_input[0], STDIN_FILENO);
    dup2(pipe_output[1], STDOUT_FILENO);
    dup2(pipe_output[1], STDERR_FILENO);

    // Create a char** for the arguments (all the contents of commandvec
    // except the first element, i.e. the command itself).
    char **args =
      reinterpret_cast<char **>(malloc((commandvec.size()) * sizeof(char *)));
    // Add all the arguments to the args array of char *.
    unsigned long i = 0;
    while(i < commandvec.size())
    {
      args[i] = strdup(commandvec[i].c_str());
      i++;
    }
    args[i] = NULL;
    execvp(commandvec[0].c_str(), args);
    // The args variable will be handled by the OS if execvp succeeds, but
    // if execvp fails then we should free it here (just in case the runtime
    // error below continues execution.)
    while(i > 0)
    {
      i--;
      free(args[i]);
    }
    free(args);
    // Only reachable if execvp failed
    // Note that here we send to std::cerr since we are in the child process
    // here and this is received by the parent process.
    std::cerr << "Launching " << commandvec[0]
              << " failed with error: " << std::strerror(errno) << std::endl;
    abort();
  }
  else
  {
    // parent process here
    // Close pipes to be used by the child process
    close(pipe_input[0]);
    close(pipe_output[1]);

    // Get stream for sending to the child process
    command_stream = fdopen(pipe_input[1], "w");
  }
#  endif
  process_state = statet::RUNNING;
}

piped_processt::~piped_processt()
{
#  ifdef _WIN32
  TerminateProcess(proc_info->hProcess, 0);
  // Disconnecting the pipes also kicks the client off, it should be killed
  // by now, but this will also force the client off.
  // Note that pipes are cleaned up by Windows when all handles to the pipe
  // are closed. Disconnect may be superfluous here.
  DisconnectNamedPipe(child_std_OUT_Rd);
  DisconnectNamedPipe(child_std_IN_Wr);
  CloseHandle(child_std_OUT_Rd);
  CloseHandle(child_std_IN_Wr);
  CloseHandle(proc_info->hProcess);
  CloseHandle(proc_info->hThread);
#  else
  // Close the parent side of the remaining pipes
  fclose(command_stream);
  // Note that the above will call close(pipe_input[1]);
  close(pipe_output[0]);
  // Send signal to the child process to terminate
  kill(child_process_id, SIGTERM);
#  endif
}

NODISCARD
piped_processt::send_responset piped_processt::send(const std::string &message)
{
  if(process_state != statet::RUNNING)
  {
    return send_responset::ERRORED;
  }
#ifdef _WIN32
  if(!WriteFile(child_std_IN_Wr, message.c_str(), message.size(), NULL, NULL))
  {
    // Error handling with GetLastError ?
    return send_responset::FAILED;
  }
#else
  // send message to solver process
  int send_status = fputs(message.c_str(), command_stream);
  fflush(command_stream);

  if(send_status == EOF)
  {
    return send_responset::FAILED;
  }
#  endif
  return send_responset::SUCCEEDED;
}

std::string piped_processt::receive()
{
  INVARIANT(
    process_state == statet::RUNNING,
    "Can only receive() from a fully initialised process");
  std::string response = std::string("");
  char buff[BUFSIZE];
  bool success = true;
#ifdef _WIN32
  DWORD nbytes;
#else
  int nbytes;
#endif
  while(success)
  {
#ifdef _WIN32
    success = ReadFile(child_std_OUT_Rd, buff, BUFSIZE, &nbytes, NULL);
#else
    nbytes = read(pipe_output[0], buff, BUFSIZE);
    // Added the status back in here to keep parity with old implementation
    // TODO: check which statuses are really used/needed.
    if(nbytes == 0) // Update if the pipe is stopped
      process_state = statet::ERRORED;
    success = nbytes > 0;
#endif
    INVARIANT(
      nbytes < BUFSIZE,
      "More bytes cannot be read at a time, than the size of the buffer");
    if(nbytes > 0)
    {
      response.append(buff, nbytes);
    }
  }
  return response;
}

std::string piped_processt::wait_receive()
{
  // can_receive(PIPED_PROCESS_INFINITE_TIMEOUT) waits an ubounded time until
  // there is some data
  can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  return receive();
}

piped_processt::statet piped_processt::get_status()
{
  return process_state;
}

bool piped_processt::can_receive(optionalt<std::size_t> wait_time)
{
  // unwrap the optional argument here
  const int timeout = wait_time ? narrow<int>(*wait_time) : -1;
#ifdef _WIN32
  int waited_time = 0;
  // The next four need to be initialised for compiler warnings
  DWORD buffer = 0;
  LPDWORD nbytes = 0;
  LPDWORD rbytes = 0;
  LPDWORD rmbytes = 0;
  while(timeout < 0 || waited_time >= timeout)
  {
    PeekNamedPipe(child_std_OUT_Rd, &buffer, 1, nbytes, rbytes, rmbytes);
    if(buffer != 0)
    {
      return true;
    }
// TODO make this define and choice better
#  define WIN_POLL_WAIT 10
    Sleep(WIN_POLL_WAIT);
    waited_time += WIN_POLL_WAIT;
  }
#else
  struct pollfd fds // NOLINT
  {
    pipe_output[0], POLLIN, 0
  };
  nfds_t nfds = POLLIN;
  const int ready = poll(&fds, nfds, timeout);

  switch(ready)
  {
  case -1:
    // Error case
    // Further error handling could go here
    process_state = statet::ERRORED;
    // fallthrough intended
  case 0:
    // Timeout case
    // Do nothing for timeout and error fallthrough, default function behaviour
    // is to return false.
    break;
  default:
    // Found some events, check for POLLIN
    if(fds.revents & POLLIN)
    {
      // we can read from the pipe here
      return true;
    }
    // Some revent we did not ask for or check for, can't read though.
  }
#  endif
  return false;
}

bool piped_processt::can_receive()
{
  return can_receive(0);
}

void piped_processt::wait_receivable(int wait_time)
{
  while(process_state == statet::RUNNING && !can_receive(0))
  {
#ifdef _WIN32
    Sleep(wait_time);
#else
    usleep(wait_time);
#endif
  }
}
