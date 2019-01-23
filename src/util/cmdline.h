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
  virtual bool parse(int argc, const char **argv, const char *optstring);

  std::string get_value(char option) const;
  std::string get_value(const char *option) const;

  const std::list<std::string> &get_values(const std::string &option) const;
  const std::list<std::string> &get_values(char option) const;

  std::list<std::string> get_comma_separated_values(const char *option) const;

  virtual bool isset(char option) const;
  virtual bool isset(const char *option) const;
  virtual void set(const std::string &option);
  virtual void set(const std::string &option, const std::string &value);
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

  std::vector<optiont> options;

  optionalt<std::size_t> getoptnr(char option) const;
  optionalt<std::size_t> getoptnr(const std::string &option) const;
};

#endif // CPROVER_UTIL_CMDLINE_H
