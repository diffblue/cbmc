/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "parse_options.h"

#include <algorithm>
#include <cctype>
#include <climits>
#include <iostream>

#if defined (_WIN32)
#define EX_OK 0
#define EX_USAGE 1
#else
#include <sysexits.h>
#endif

#include "cmdline.h"
#include "config.h"
#include "exception_utils.h"
#include "exit_codes.h"
#include "signal_catcher.h"
#include "string_utils.h"
#include "version.h"

parse_options_baset::parse_options_baset(
  const std::string &_optstring,
  int argc,
  const char **argv,
  const std::string &program)
  : parse_result(cmdline.parse(
      argc,
      argv,
      (std::string("?h(help)") + _optstring).c_str())),
    ui_message_handler(cmdline, program),
    log(ui_message_handler)
{
}

void parse_options_baset::help()
{
}

void parse_options_baset::usage_error()
{
  log.error() << "Usage error!\n" << messaget::eom;
  help();
}

/// Print an error message mentioning the option that was not recognized when
/// parsing the command line.
void parse_options_baset::unknown_option_msg()
{
  if(!cmdline.unknown_arg.empty())
  {
    log.error() << "Unknown option: " << cmdline.unknown_arg;
    auto const suggestions =
      cmdline.get_argument_suggestions(cmdline.unknown_arg);
    if(!suggestions.empty())
    {
      log.error() << ", did you mean ";
      if(suggestions.size() > 1)
      {
        log.error() << "one of ";
      }
      join_strings(log.error(), suggestions.begin(), suggestions.end(), ", ");
      log.error() << "?";
    }
    log.error() << messaget::eom;
  }
}

int parse_options_baset::main()
{
  // catch all exceptions here so that this code is not duplicated
  // for each tool
  try
  {
    if(parse_result)
    {
      usage_error();
      unknown_option_msg();
      return EX_USAGE;
    }

    if(cmdline.isset('?') || cmdline.isset('h') || cmdline.isset("help"))
    {
      help();
      return EX_OK;
    }

    // install signal catcher
    install_signal_catcher();

    return doit();
  }

  // CPROVER style exceptions in order of decreasing happiness
  catch(const invalid_command_line_argument_exceptiont &e)
  {
    log.error() << e.what() << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  catch(const cprover_exception_baset &e)
  {
    log.error() << e.what() << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(const std::string &e)
  {
    log.error() << "C++ string exception : " << e << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(const char *e)
  {
    log.error() << "C string exception : " << e << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(int e)
  {
    log.error() << "Numeric exception : " << e << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  // C++ style exceptions
  catch(const std::bad_alloc &)
  {
    log.error() << "Out of memory" << messaget::eom;
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }
  catch(const std::exception &e)
  {
    log.error() << e.what() << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(const invariant_failedt &e)
  {
    log.error() << e.what() << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(...)
  {
    log.error() << "Unknown exception type!" << messaget::eom;
    return CPROVER_EXIT_EXCEPTION;
  }
}

void parse_options_baset::log_version_and_architecture(
  const std::string &front_end)
{
  log.status() << front_end << " version " << CBMC_VERSION << " "
               << sizeof(void *) * CHAR_BIT << "-bit "
               << config.this_architecture() << " "
               << config.this_operating_system() << messaget::eom;
}

std::string align_center_with_border(const std::string &text)
{
  auto const total_length = std::size_t{63};
  auto const border = std::string{"* *"};
  auto const fill =
    total_length - std::min(total_length, 2 * border.size() + text.size());
  auto const fill_right = fill / 2;
  auto const fill_left = fill - fill_right;
  return border + std::string(fill_left, ' ') + text +
         std::string(fill_right, ' ') + border;
}

std::string
banner_string(const std::string &front_end, const std::string &version)
{
  const std::string version_str = front_end + " " + version + " " +
                                  std::to_string(sizeof(void *) * CHAR_BIT) +
                                  "-bit";

  return align_center_with_border(version_str);
}

std::string help_entry(
  const std::string &option,
  const std::string &description,
  const std::size_t left_margin,
  const std::size_t width)
{
  PRECONDITION(!option.empty());
  PRECONDITION(!std::isspace(option.front()));
  PRECONDITION(!std::isspace(option.back()));
  PRECONDITION(option.length() <= width);

  PRECONDITION(!description.empty());
  PRECONDITION(!std::isspace(description.front()));
  PRECONDITION(!std::isspace(description.back()));

  PRECONDITION(left_margin < width);

  std::string result;

  if(option.length() >= left_margin - 1)
  {
    result = " " + option + "\n";
    result += wrap_line(description, left_margin, width) + "\n";

    return result;
  }

  std::string padding(left_margin - option.length() - 1, ' ');
  result = " " + option + padding;

  if(description.length() <= (width - left_margin))
  {
    return result + description + "\n";
  }

  auto it = description.cbegin() + (width - left_margin);
  auto rit = std::reverse_iterator<decltype(it)>(it) - 1;

  auto rit_space = std::find(rit, description.crend(), ' ');
  auto it_space = rit_space.base() - 1;
  CHECK_RETURN(*it_space == ' ');

  result.append(description.cbegin(), it_space);
  result.append("\n");

  result +=
    wrap_line(it_space + 1, description.cend(), left_margin, width) + "\n";

  return result;
}
