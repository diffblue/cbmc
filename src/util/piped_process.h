/// \file piped_process.h
/// Subprocess communication with pipes
/// \author Diffblue Ltd.

#ifndef CPROVER_UTIL_PIPED_PROCESS_H
#define CPROVER_UTIL_PIPED_PROCESS_H

#ifdef _WIN32
// TODO: Windows definitions go here
#else

#  include <vector>

#  include "optional.h"

#  define PIPED_PROCESS_INFINITE_TIMEOUT                                       \
    optionalt<std::size_t>                                                     \
    {                                                                          \
    }

class piped_processt
{
public:
  /// Enumeration to keep track of child process state.
  enum class statet
  {
    NOT_CREATED,
    CREATED,
    STOPPED,
    ERROR
  };

  /// Enumeration for send response.
  enum class send_responset
  {
    SUCCEEDED,
    FAILED,
    ERROR
  };

  /// Send a string message (command) to the child process.
  /// \param message The string message to be sent.
  /// \return
  send_responset send(const std::string &message);
  /// Read a string from the child process' output.
  /// \return a string containing data from the process, empty string if no data
  std::string receive();
  /// Wait until a string is available and read a string from the child
  /// process' output.
  /// \return a string containing data from the process, empty string if no data
  std::string wait_receive();

  /// Get child process status.
  /// \return a statet representing the status of the child process
  statet get_status();

  /// See if this process can receive data from the other process.
  /// \param wait_time Amount of time to wait before timing out, with:
  ///        * positive integer being wait time in milli-seconds,
  ///        * 0 signifying non-blocking immediate return, and
  ///        * an empty optional representing infinite wait time.
  /// \return true is there is data to read from process, false otherwise
  bool can_receive(optionalt<std::size_t> wait_time);

  /// See if this process can receive data from the other process.
  /// Note this calls can_receive(0);
  /// \return true if there is data to read from process, false otherwise.
  bool can_receive();

  /// Wait for the pipe to be ready, waiting specified time between
  /// checks. Will return when the pipe is ready or the other process
  /// is not in a statet::CREATED state (i.e. error has occured).
  /// \param wait_time Time spent in usleep() (microseconds) between checks
  //         of can_receive(0)
  void wait_receivable(int wait_time);

  /// Initiate a new subprocess with pipes supporting communication
  /// between the parent (this process) and the child.
  /// \param commandvec The command and arguments to create the process
  explicit piped_processt(const std::vector<std::string> commandvec);

  ~piped_processt();

protected:
  // Child process ID.
  pid_t child_process_id;
  FILE *command_stream;
  // The member fields below are so named from the perspective of the
  // parent -> child process. So `pipe_input` is where we are feeding
  // commands to the child process, and `pipe_output` is where we read
  // the results of execution from.
  int pipe_input[2];
  int pipe_output[2];
  statet process_state;
};

#endif // endif _WIN32

#endif // endifndef CPROVER_UTIL_PIPED_PROCESS_H
