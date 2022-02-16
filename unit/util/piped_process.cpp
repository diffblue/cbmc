/// \file
/// \author Diffblue Ltd.
/// Unit tests for checking the piped process communication mechanism.

#include <util/optional.h>
#include <util/piped_process.h>
#include <util/string_utils.h>

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

// Used for testing destructor/timing
#include <chrono>

TEST_CASE(
  "Creating a sub process and reading its output.",
  "[core][util][piped_process]")
{
  const std::string to_be_echoed = "The Jabberwocky";
  // Need to give path to avoid shell built-in invocation
  std::vector<std::string> commands;
#ifdef _WIN32
  commands.push_back("cmd /c echo The Jabberwocky");
#else
  commands.push_back("/bin/echo");
  commands.push_back(to_be_echoed);
#endif
  piped_processt process(commands, null_message_handler);

  // This is an indirect way to detect when the pipe has something. This
  // could (in theory) also return when there is an error, but this unit
  // test is not doing error handling.
  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = strip_string(process.receive());

  REQUIRE(response == to_be_echoed);
}

TEST_CASE(
  "Creating a sub process with a binary that doesn't exist.",
  "[core][util][piped_process]")
{
  std::vector<std::string> commands;
#ifdef _WIN32
  const std::string expected_error("'abcde' is not recognized");
  commands.push_back("cmd /c abcde");
#else
  const std::string expected_error("Launching abcde failed");
  commands.push_back("abcde");
#endif
  piped_processt process(commands, null_message_handler);

  // This is an indirect way to detect when the pipe has something. This
  // could (in theory) also return when there is an error, but this unit
  // test is not doing error handling.
  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = process.receive();
  // This tracks how many times we tried, if for some reason we are stuck
  // give up eventually for this test.
  int too_many_tries = 0;
  // The expected length of the output string is 6 characters, keep
  // trying up to the retry limit of 5 or the string is long enough
  while(too_many_tries < 5 && response.length() < 64)
  {
    // Wait a short amount of time to try and receive
    process.can_receive(10);
    response += process.receive();
    too_many_tries++;
  }

  REQUIRE(response.find(expected_error) < response.length() - 5);
}

// This is a test of child termination, it's not perfect and could go wrong
// if run at midnight, but it's sufficient for a basic check for now.
TEST_CASE(
  "Creating a sub process and terminate it.",
  "[core][util][piped_process]")
{
  std::vector<std::string> commands;
#ifdef _WIN32
  commands.push_back("cmd /c ping 127.0.0.1 -n 6 > nul");
  std::chrono::steady_clock::time_point start_time =
    std::chrono::steady_clock::now();
  {
    // Scope restriction to cause destruction
    piped_processt process(commands, null_message_handler);
  }
  std::chrono::steady_clock::time_point end_time =
    std::chrono::steady_clock::now();
  std::chrono::duration<double> time_span =
    std::chrono::duration_cast<std::chrono::duration<double>>(
      end_time - start_time);
  size_t calc = time_span.count();
#else
  // Currently not working under Linux/MacOS?!
  // Likely due to issue in handling signals from child process
#  if 0
  commands.push_back("sleep 6");
  time_t calc = time(NULL);
  piped_processt process(commands, null_message_handler);
  process.~piped_processt();
  calc = time(NULL) - calc;
#  else
  size_t calc = 0;
#  endif
#endif
  // Command should take >5 seconds, check we called destructor and
  // moved on in less than 2 seconds.
  REQUIRE(calc < 2);
}

TEST_CASE(
  "Creating a sub process of z3 and read a response from an echo command.",
  "[core][util][piped_process][.z3]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  piped_processt process(commands, null_message_handler);

  REQUIRE(
    process.send("(echo \"hi\")\n") ==
    piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = strip_string(process.receive());
  REQUIRE(response == "hi");

  REQUIRE(
    process.send("(exit)\n") == piped_processt::send_responset::SUCCEEDED);
}

TEST_CASE(
  "Creating a sub process and interacting with it.",
  "[core][util][piped_process][.z3]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  const std::string termination_statement = "(exit)\n";
  piped_processt process(commands, null_message_handler);

  REQUIRE(
    process.send("(echo \"hi\")\n") ==
    piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = strip_string(process.receive());
  REQUIRE(response == "hi");

  std::string statement = std::string("(echo \"Second string\")\n");
  REQUIRE(process.send(statement) == piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  response = strip_string(process.receive());
  REQUIRE(response == "Second string");

  REQUIRE(
    process.send(termination_statement) ==
    piped_processt::send_responset::SUCCEEDED);
}

TEST_CASE(
  "Use a created piped process instance of z3 to solve a simple SMT problem",
  "[core][util][piped_process][.z3]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  commands.push_back("-smt2");
  piped_processt process(commands, null_message_handler);

  std::string message =
    "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert (> "
    "(+ (mod x 4) (* 3 (div y 2))) (- x y)))  (check-sat)\n";
  REQUIRE(process.send(message) == piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = strip_string(process.receive());
  REQUIRE(response == "sat");

  REQUIRE(
    process.send("(exit)\n") == piped_processt::send_responset::SUCCEEDED);
}

TEST_CASE(
  "Use a created piped process instance of z3 to solve a simple SMT problem "
  "with wait_receive",
  "[core][util][piped_process][.z3]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  commands.push_back("-smt2");
  piped_processt process(commands, null_message_handler);

  std::string statement =
    "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert (> "
    "(+ (mod x 4) (* 3 (div y 2))) (- x y)))  (check-sat)\n";

  REQUIRE(process.send(statement) == piped_processt::send_responset::SUCCEEDED);

  std::string response = strip_string(process.wait_receive());
  REQUIRE(response == "sat");

  REQUIRE(
    process.send("(exit)\n") == piped_processt::send_responset::SUCCEEDED);
}

TEST_CASE(
  "Use a created piped process instance of z3 to test wait_receivable",
  "[core][util][piped_process]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  piped_processt process(commands, null_message_handler);

  REQUIRE(
    process.send("(echo \"hi\")\n") ==
    piped_processt::send_responset::SUCCEEDED);

  process.wait_receivable(100);
  std::string response = strip_string(process.receive());
  REQUIRE(response == "hi");

  std::string statement = std::string("(echo \"Second string\")\n");
  REQUIRE(process.send(statement) == piped_processt::send_responset::SUCCEEDED);

  process.wait_receivable(100);
  response = strip_string(process.receive());
  REQUIRE(response == "Second string");

  REQUIRE(
    process.send("(exit)\n") == piped_processt::send_responset::SUCCEEDED);
}

TEST_CASE(
  "Use piped process instance of z3 to solve a simple SMT problem and get the "
  "model, with wait_receivable/can_receive",
  "[core][util][piped_process][.z3]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  commands.push_back("-smt2");
  piped_processt process(commands, null_message_handler);

  std::string statement =
    "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert (> "
    "(+ (mod x 4) (* 3 (div y 2))) (- x y)))  (check-sat)\n";
  REQUIRE(process.send(statement) == piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = strip_string(process.receive());
  REQUIRE(response == "sat");

  REQUIRE(
    process.send("(get-model)\n") == piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  // If we receive here we can get less than the full (expected) output.
  // The normal expectation is that the caller will handle parsing and
  // checking of the received data (i.e. it is not the responsibility
  // of the piped_process to know how big the response should be).
  // Therefore, we need to rebuild the string here.
  response = process.receive();
  // This tracks how many times we tried, if for some reason we are stuck
  // give up eventually for this test.
  int too_many_tries = 0;
  // The expected length of the output string is 74 characters, keep
  // trying up to the retry limit of 5 or the string is long enough
  while(too_many_tries < 5 && response.length() < 74)
  {
    // Wait a short amount of time to try and receive
    process.can_receive(10);
    response += process.receive();
    too_many_tries++;
  }
  // It would be nice to check then whole model, but this is non-deterministic
  // and so causes problems.
  // Note that the above loop would need to read 74 characters to safely check
  // the model commented out here.
  // const std::string expected_response = std::string(
  //   "(model \n  (define-fun y () Int\n    0)\n  "
  //   "(define-fun x () Int\n    (- 4))\n)\n");
  // REQUIRE(response == expected_response);
  REQUIRE(response.find("(define-fun") != std::string::npos);

  REQUIRE(
    process.send("(exit)\n") == piped_processt::send_responset::SUCCEEDED);
}

TEST_CASE(
  "Use a created piped process instance of z3 to solve a simple SMT problem "
  "and get the model, using infinite wait can_receive(...)",
  "[core][util][piped_process][.z3]")
{
  std::vector<std::string> commands;
  commands.push_back("z3");
  commands.push_back("-in");
  commands.push_back("-smt2");
  piped_processt process(commands, null_message_handler);

  std::string statement =
    "(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert (> "
    "(+ (mod x 4) (* 3 (div y 2))) (- x y)))  (check-sat)\n";
  REQUIRE(process.send(statement) == piped_processt::send_responset::SUCCEEDED);

  process.can_receive(PIPED_PROCESS_INFINITE_TIMEOUT);
  std::string response = strip_string(process.receive());
  REQUIRE(response == "sat");

  REQUIRE(
    process.send("(exit)\n") == piped_processt::send_responset::SUCCEEDED);
}
