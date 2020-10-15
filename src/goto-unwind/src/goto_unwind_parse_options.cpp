/// \file
/// \author Diffblue Ltd.

#include "goto_unwind_parse_options.h"

#include <cstddef>
#include <iostream>
#include <string>
#include <utility>

#include <goto-instrument/unwind.h>
#include <goto-instrument/unwindset.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/write_goto_binary.h>
#include <util/exit_codes.h>
#include <util/string2int.h>
#include <util/validate.h>
#include <util/version.h>

goto_unwind_parse_optionst::goto_unwind_parse_optionst(
  int argc,
  const char **argv)
  : parse_options_baset("(unwind-limit):", argc, argv, "goto-unwind")
{
}

struct goto_unwind_optionst
{
  std::size_t unwind_limit;
  std::string source_goto_binary_filepath;
  std::string destination_goto_binary_filepath;

  static constexpr const char *unwind_limit_option_name = "unwind-limit";
  static constexpr size_t unwind_limit_default_value = 10;

  static std::ostream &help(std::ostream &log)
  {
    log << "--" << unwind_limit_option_name
        << " N    How far to unwind (default: " << unwind_limit_default_value
        << ")\n";
    return log;
  }

  /// Parse an integral-type option. Returns nullopt if the option was not
  /// passed, returns a filled-in option with the value that was passed if the
  /// option was passed, throws an exception if the option was passed but the
  /// option value couldn't be parsed.
  template <typename T>
  static optionalt<T> parse_int_option(
    const cmdlinet &cmdline,
    const std::string &option_name,
    const std::string &error_message)
  {
    if(cmdline.isset(option_name.c_str()))
    {
      if(
        auto option_value =
          string2optional<T>(cmdline.get_value(option_name.c_str())))
      {
        return option_value;
      }
      else
      {
        throw invalid_command_line_argument_exceptiont{
          error_message +
            "(value was: " + cmdline.get_value(option_name.c_str()) + ")",
          "--" + option_name};
      }
    }
    return nullopt;
  }

  static goto_unwind_optionst from_cmdline(const cmdlinet &cmdline)
  {
    goto_unwind_optionst options{};

    if(cmdline.args.size() == 1)
    {
      options.source_goto_binary_filepath =
        options.destination_goto_binary_filepath = cmdline.args[0];
    }
    else if(cmdline.args.size() == 2)
    {
      options.source_goto_binary_filepath = cmdline.args[0];
      options.destination_goto_binary_filepath = cmdline.args[1];
    }
    else
    {
      throw invalid_command_line_argument_exceptiont{
        "Expecting either a single binary to read from and modify, or both a "
        "source and a destination binary",
        "<Source binary> [<Destination binary>]"};
    }

    options.unwind_limit =
      parse_int_option<std::size_t>(
        cmdline, unwind_limit_option_name, "couldn't parse as size_t")
        .value_or(unwind_limit_default_value);
    return options;
  }
};

// due to an interesting quirk with C++11 we do need to define these
// even if they are static constexpr... C++17 removed this limitation
// so if we ever manage to upgrade please remove these lines and forget
// they ever existed.
constexpr const char *goto_unwind_optionst::unwind_limit_option_name;
constexpr size_t goto_unwind_optionst::unwind_limit_default_value;

int goto_unwind_parse_optionst::doit()
{
  const auto options = goto_unwind_optionst::from_cmdline(cmdline);
  auto goto_model = get_goto_model(options.source_goto_binary_filepath);
  do_unwind(goto_model, options.unwind_limit);
  write_goto_binary(
    options.destination_goto_binary_filepath,
    goto_model,
    log.get_message_handler());
  return CPROVER_EXIT_SUCCESS;
}
void goto_unwind_parse_optionst::help()
{
  log.status() << banner_string("goto-unwind", CBMC_VERSION) << '\n'
               << align_center_with_border("Copyright (C) 2020") << '\n'
               << align_center_with_border("Diffblue Ltd.") << '\n' // NOLINT(*)
               << align_center_with_border("cbmc@diffblue.com")
               << '\n' // NOLINT(*)
               << '\n'
               << goto_unwind_optionst::help;

  log.status() << messaget::eom;
}

goto_modelt
goto_unwind_parse_optionst::get_goto_model(const std::string &goto_binary_path)
{
  auto goto_model = [&goto_binary_path, this]() {
    if(auto goto_model = read_goto_binary(goto_binary_path, ui_message_handler))
    {
      return std::move(*goto_model);
    }
    throw invalid_source_file_exceptiont{"Failed to read goto model from " +
                                         goto_binary_path};
  }();

  // function pointers need to be removed for unwinding to take place
  const bool add_safety_assertion = true;
  const bool only_remove_const_fps = false;
  remove_function_pointers(
    ui_message_handler,
    goto_model,
    add_safety_assertion,
    only_remove_const_fps);

  return goto_model;
}

void goto_unwind_parse_optionst::do_unwind(
  goto_modelt &model,
  const size_t limit)
{
  unwindsett unwindset{};
  goto_unwindt unwind{};
  unwindset.parse_unwind(std::to_string(limit));
  unwind(model, unwindset, goto_unwindt::unwind_strategyt::ASSERT);
  model.goto_functions.update();
}
