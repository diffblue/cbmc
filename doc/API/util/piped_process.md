# `src/util/piped_process.{cpp, h}`

To utilise the `piped_process` API for interprocess communication with any binary:

* You need to initialise it by calling the construct `piped_processt("binary with args")`.
  * If IPC fails before child process creation, you will get a `system_exceptiont`.
  * If the `binary command` does not correspond to a binary in the `$PATH` or is
    not a path to a binary itself, you'll read a string `Launching <xyz> failed with error: <error>`
    when you attempt to `receive()` output from the child process.
* The child process is automatically killed with SIGTERM when the destructor for
  the `piped_processt` object is called.
  * This will occur automatically when the `piped_processt` goes out of scope if
    it's locally scoped.
* Use `send()` to send a string message to the child process' input.
  * This returns a `send_responset`, an enum that shows whether the
    sending of the message through the pipe succeeded or failed.
* Use `receive()` to read a string message from the child process' output.
  * It's always a good idea to guard a call to `receive` with `can_receive()`,
    so that receiving is blocked until there's something to receive.
    * `can_receive` with no arguments will default to infinite wait time for piped
      process readiness.
  * Alternatively, you can guard the call to `receive` with `wait_receivable`.
   `wait_receivable` takes an integer value representing `microseconds` of waiting
   time between checks for pipe readiness.
