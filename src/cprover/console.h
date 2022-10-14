/*******************************************************************\

Module: Console

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Console

#ifndef CPROVER_CPROVER_CONSOLE_H
#define CPROVER_CPROVER_CONSOLE_H

#include <cstddef>
#include <iosfwd>

class consolet
{
public:
  static void init();

  // colors
  static std::ostream &blue(std::ostream &);
  static std::ostream &cyan(std::ostream &);
  static std::ostream &green(std::ostream &);
  static std::ostream &red(std::ostream &);
  static std::ostream &yellow(std::ostream &);
  static std::ostream &orange(std::ostream &);

  static std::ostream &bold(std::ostream &);
  static std::ostream &faint(std::ostream &);
  static std::ostream &underline(std::ostream &);

  static std::ostream &reset(std::ostream &);

  // cursor movement
  static std::ostream &cursorup(std::ostream &);

  // deletion
  static std::ostream &cleareol(std::ostream &); // erase to end of line

  static bool is_terminal()
  {
    init();
    return _is_terminal;
  }

  static bool use_SGR()
  {
    init();
    return _use_SGR;
  }

  static std::ostream &out()
  {
    init();
    return *_out;
  }

  static std::ostream &err()
  {
    init();
    return *_err;
  }

  static std::size_t width();

  // -1: not printable
  //  0: no width
  //  1: usual single width
  //  2: double width
  static int wcwidth(wchar_t);

  // redirection
  class redirectt
  {
  public:
    // __out has some meaning on Windows, therefore using __console_out
    redirectt(std::ostream &__console_out, std::ostream &__console_err);
    ~redirectt();

  protected:
    std::ostream *old_out = nullptr, *old_err = nullptr;
    bool old_is_terminal = false;
  };

protected:
  static bool _is_terminal;
  static bool _use_SGR;
  static bool _init_done;
  static std::size_t _width;
  static bool _width_is_set;
  static std::ostream *_out;
  static std::ostream *_err;
};

#endif // CPROVER_CPROVER_CONSOLE_H
