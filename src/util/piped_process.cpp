/// \file piped_process.cpp
/// Subprocess communication with pipes.
/// \author Diffblue Ltd.

#ifdef _WIN32
// Windows includes go here
#else
#  include <fcntl.h>  // library for fcntl function
#  include <poll.h>   // library for poll function
#  include <signal.h> // library for kill function
#  include <unistd.h> // library for read/write/sleep/etc. functions
#endif

#ifdef _WIN32
// Unimplemented on windows for now...
#else

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

piped_processt::piped_processt(const std::vector<std::string> commandvec)
{
#  ifdef _WIN32
  UNIMPLEMENTED_FEATURE("Pipe IPC on windows.")
#  else

  if(pipe(pipe_input) == -1)
  {
    throw system_exceptiont("Input pipe creation failed");
  }

  if(pipe(pipe_output) == -1)
  {
    throw system_exceptiont("Output pipe creation failed");
  }

  // Default state
  process_state = statet::NOT_CREATED;

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
    process_state = statet::CREATED;
  }
#  endif
}

piped_processt::~piped_processt()
{
#  ifdef _WIN32
  UNIMPLEMENTED_FEATURE("Pipe IPC on windows: piped_processt constructor")
#  else
  // Close the parent side of the remaining pipes
  fclose(command_stream);
  // Note that the above will call close(pipe_input[1]);
  close(pipe_output[0]);
  // Send signal to the child process to terminate
  kill(child_process_id, SIGTERM);
#  endif
}

piped_processt::send_responset piped_processt::send(const std::string &message)
{
#  ifdef _WIN32
  UNIMPLEMENTED_FEATURE("Pipe IPC on windows: send()")
#  else

  if(process_state != statet::CREATED)
  {
    return send_responset::ERROR;
  }

  // send message to solver process
  int send_status = fputs(message.c_str(), command_stream);
  fflush(command_stream);

  if(send_status == EOF)
  {
    return send_responset::FAILED;
  }

  return send_responset::SUCCEEDED;
#  endif
}

std::string piped_processt::receive()
{
#  ifdef _WIN32
  UNIMPLEMENTED_FEATURE("Pipe IPC on windows: receive()")
#  else

  INVARIANT(
    process_state == statet::CREATED,
    "Can only receive() from a fully initialised process");

  std::string response = std::string("");
  int nbytes;
  char buff[BUFSIZE];

  while(true)
  {
    nbytes = read(pipe_output[0], buff, BUFSIZE);
    INVARIANT(
      nbytes < BUFSIZE,
      "More bytes cannot be read at a time, than the size of the buffer");
    switch(nbytes)
    {
    case -1:
      // Nothing more to read in the pipe
      return response;
    case 0:
      // Pipe is closed.
      process_state = statet::STOPPED;
      return response;
    default:
      // Read some bytes, append them to the response and continue
      response.append(buff, nbytes);
    }
  }

  UNREACHABLE;
#  endif
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
#  ifdef _WIN32
  UNIMPLEMENTED_FEATURE(
    "Pipe IPC on windows: can_receive(optionalt<std::size_t> wait_time)")
#  else
  // unwrap the optional argument here
  const int timeout = wait_time ? narrow<int>(*wait_time) : -1;
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
    process_state = statet::ERROR;
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
  return false;
#  endif
}

bool piped_processt::can_receive()
{
  return can_receive(0);
}

void piped_processt::wait_receivable(int wait_time)
{
#  ifdef _WIN32
  UNIMPLEMENTED_FEATURE("Pipe IPC on windows: wait_stopped(int wait_time)")
#  else
  while(process_state == statet::CREATED && !can_receive(0))
  {
    usleep(wait_time);
  }
#  endif
}

#endif
