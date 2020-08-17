/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_CMDLINE_H
#define CPROVER_UTIL_CMDLINE_H

#include <limits>
#include <list>
#include <string>
#include <vector>

#include "optional.h"

class cmdlinet
{
public:
  /// Parses a commandline according to a specification given in \p optstring.
  /// \param argc How many arguments there are.
  /// \param argv An array of C strings.
  ///             The 0th element is assumed to be the name of the command as
  ///             it was invoked (e.g. /usr/bin/cmake) and is ignored. It is
  ///             further assumed the array holds \p argc+1 elements with the C
  ///             string at index argc being a terminating null pointer.
  ///             This argument is parsed based on \p optstring.
  /// \param optstring A specification of allowed command line options.
  ///                  This is a C string container any number of single
  ///                  characters other than '(', ')' or ':' signifying a
  ///                  "short" option consisting of just that character, or
  ///                  names consisting of any characters other than ')'
  ///                  surrounded by a matching pair of '(' and ')' signifying a
  ///                  "long" option with the name being the string between '('
  ///                  and ')', both of which can be optionally followed by a
  ///                  single ':' indicating that the option takes a argument,
  ///                  if not present it does not. arguments must be in the
  ///                  next array element in \p argv , except for short options
  ///                  whose argument may also be concatenated directly on them.
  ///
  ///                  Option names in \p argv must start with either '-' or "--",
  ///                  no distinction between long and short options is made
  ///                  here, although it is customary to use only one '-' for
  ///                  short options and "--" for long options.
  ///
  ///                  All options are optional, if some are required it is up
  ///                  to the user to check that they are present.
  ///
  ///                  Examples:
  ///
  ///                  argc = 4
  ///                  argv = `{"name", "-V", "--name", "CProver", nullptr}`
  ///                  opstring = `"V(version)(name):"`
  ///
  ///                  here the argument to "name" would be "CProver", and
  ///                  "V" is a short option passed without arguments.
  ///
  ///                  argc = 3
  ///                  argv = `{"other-name", "-fFilename", "--trace", nullptr}`
  ///                  optstring = `"f:(trace)(some-other-option):G"`
  ///
  ///                  here the argument to option "f" would be "Filename",
  ///                  "trace" is a long option with no argument, and
  ///                  "some-other-option" and "G" are both allowed options that
  ///                  don’t appear on the commandline (with and without
  ///                  argument respectively).
  ///
  /// \return true if there was an error while parsing argv, false otherwise. If
  ///              this failed due to an unknown option name being in argv, the
  ///              public variable cmdlinet::unknown_arg will be non-empty and
  ///              contain the name of that option.
  virtual bool parse(int argc, const char **argv, const char *optstring);

  std::string get_value(char option) const;
  std::string get_value(const char *option) const;

  const std::list<std::string> &get_values(const std::string &option) const;
  const std::list<std::string> &get_values(char option) const;

  std::list<std::string> get_comma_separated_values(const char *option) const;

  virtual bool isset(char option) const;
  virtual bool isset(const char *option) const;
  /// Set option \p option to \p value, or \c true if the value is omitted.
  virtual void set(const std::string &option, bool value = true);
  virtual void set(const std::string &option, const std::string &value);
  virtual void set(const std::string &option, const char *value)
  {
    set(option, std::string{value});
  }

  virtual void clear();

  bool has_option(const std::string &option) const
  {
    return getoptnr(option).has_value();
  }

  struct option_namest
  {
    explicit option_namest(const cmdlinet &command_line);
    struct option_names_iteratort
      : public std::iterator<std::forward_iterator_tag, std::string>
    {
      option_names_iteratort() = default;
      explicit option_names_iteratort(
        const cmdlinet *command_line,
        std::size_t index);
      option_names_iteratort(const option_names_iteratort &other) = default;
      option_names_iteratort(option_names_iteratort &&other) = default;
      option_names_iteratort &
      operator=(const option_names_iteratort &) = default;
      option_names_iteratort &operator=(option_names_iteratort &&) = default;

      option_names_iteratort &operator++();
      const option_names_iteratort operator++(int);
      const std::string &operator*();

      bool operator==(const option_names_iteratort &other);
      bool operator!=(const option_names_iteratort &other);

    private:
      const cmdlinet *command_line = nullptr;
      std::size_t index = std::numeric_limits<std::size_t>::max();
      bool is_valid_index() const;
      void goto_next_valid_index();
    };
    option_names_iteratort begin();
    option_names_iteratort end();

  private:
    const cmdlinet &command_line;
  };

  /// Pseudo-object that can be used to iterate over
  /// options in this cmdlinet (should not outlive this)
  option_namest option_names() const;

  typedef std::vector<std::string> argst;
  argst args;
  std::string unknown_arg;

  cmdlinet();
  virtual ~cmdlinet();

  std::vector<std::string>
  get_argument_suggestions(const std::string &unknown_argument);

protected:
  struct optiont
  {
    bool isset;
    bool hasval;
    bool islong;
    char optchar;
    std::string optstring;
    std::list<std::string> values;
  public:
    optiont():
      isset(false),
      hasval(false),
      islong(false),
      optchar(0)
    {}
  };

  /// Parses an optstring and writes the result to cmdlinet::options.
  /// It is considered a logic error to pass an invalid option string here.
  /// \see cmdlinet::parse(int,const char**,const char*)
  ///         for details on the format of the optstring
  void parse_optstring(const char *optstring);

  /// Parses a commandline according to a previously parsed optstring and
  /// writes the result to cmdlinet::options.
  /// \see cmdlinet::parse(int,const char**,const char*)
  ///         for details the meaning of argc and argv
  bool parse_arguments(int argc, const char **argv);

  std::vector<optiont> options;

  optionalt<std::size_t> getoptnr(char option) const;
  optionalt<std::size_t> getoptnr(const std::string &option) const;
};

#endif // CPROVER_UTIL_CMDLINE_H
