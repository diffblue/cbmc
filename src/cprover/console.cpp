/*******************************************************************\

Module: Console

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "console.h"

#include <cctype>
#include <iostream>
#include <sstream>

#ifdef _WIN32
#  include <io.h>
#  include <windows.h>
#  define isatty _isatty
#else
#  include <unistd.h>
#endif

#include <util/run.h>
#include <util/string_utils.h>
#include <util/unicode.h>

#ifdef _WIN32
class windows_coutt : public std::streambuf
{
public:
  // this turns UTF8 into Windows UTF16
  std::streamsize xsputn(const char_type *s, std::streamsize n) override
  {
    if(consolet::is_terminal())
    {
      auto wide_string = widen(std::string(s, n));
      DWORD number_written;
      HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
      WriteConsoleW(
        h,
        wide_string.c_str(),
        (DWORD)wide_string.size(),
        &number_written,
        nullptr);
    }
    else
    {
      std::cout.write(s, n);
    }

    return n;
  }

  int_type overflow(int_type c) override
  {
    if(consolet::is_terminal())
      std::wcout << wchar_t(c);
    else
      std::cout << char(c);
    return wchar_t(c);
  }
} windows_cout;
#endif

bool consolet::_is_terminal = false;
bool consolet::_use_SGR = false;
bool consolet::_init_done = false;
std::ostream *consolet::_out = nullptr;
std::ostream *consolet::_err = nullptr;

void consolet::init()
{
  if(_init_done)
    return;

  _init_done = true;
  _is_terminal = isatty(1);

  _out = &std::cout;
  _err = &std::cerr;

#ifdef _WIN32
  if(_is_terminal)
  {
    HANDLE out_handle = GetStdHandle(STD_OUTPUT_HANDLE);

    DWORD consoleMode;
    if(GetConsoleMode(out_handle, &consoleMode))
    {
      consoleMode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
      if(SetConsoleMode(out_handle, consoleMode))
        _use_SGR = true;
    }

    std::cout.rdbuf(&windows_cout);
  }
#else
  _use_SGR = true;
#endif
}

std::ostream &consolet::blue(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[34m";
  else
    return str;
}

std::ostream &consolet::cyan(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[36m";
  else
    return str;
}

std::ostream &consolet::green(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[32m";
  else
    return str;
}

std::ostream &consolet::red(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[31m";
  else
    return str;
}

std::ostream &consolet::yellow(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[33m";
  else
    return str;
}

std::ostream &consolet::orange(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[38;5;214m";
  else
    return str;
}

std::ostream &consolet::bold(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[1m";
  else
    return str;
}

std::ostream &consolet::faint(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[2m";
  else
    return str;
}

std::ostream &consolet::underline(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[4m";
  else
    return str;
}

std::ostream &consolet::reset(std::ostream &str)
{
  if(is_terminal() && use_SGR())
    return str << "\x1b[m";
  else
    return str;
}

std::size_t consolet::width()
{
  std::size_t width = 80; // default

  if(_is_terminal)
  {
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    CONSOLE_SCREEN_BUFFER_INFO info;
    GetConsoleScreenBufferInfo(h, &info);
    width = info.srWindow.Right - info.srWindow.Left + 1;
#else
    std::ostringstream width_stream;
    run("stty", {"stty", "size"}, "", width_stream, "");
    auto stty_output = split_string(width_stream.str(), ' ');
    if(
      stty_output.size() >= 1 && !stty_output[1].empty() &&
      isdigit(stty_output[1][0]))
    {
      auto width_l = atol(stty_output[1].c_str());
      if(width_l >= 10 && width_l <= 400)
        width = width_l;
    }
#endif
  }

  return width;
}

extern "C" int mk_wcwidth(wchar_t ucs);

int consolet::wcwidth(wchar_t ucs)
{
  return mk_wcwidth(ucs);
}

consolet::redirectt::redirectt(
  std::ostream &__console_out,
  std::ostream &__console_err)
{
  consolet::init();
  old_out = consolet::_out;
  old_err = consolet::_err;
  old_is_terminal = consolet::_is_terminal;
  consolet::_out = &__console_out;
  consolet::_err = &__console_err;
  consolet::_is_terminal = false;
}

consolet::redirectt::~redirectt()
{
  consolet::_out = old_out;
  consolet::_err = old_err;
  consolet::_is_terminal = old_is_terminal;
}
