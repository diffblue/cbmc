/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_COUT_MESSAGE_H
#define CPROVER_UTIL_COUT_MESSAGE_H

#include "message.h"

class cout_message_handlert:public stream_message_handlert
{
public:
  // all messages go to stdout
  cout_message_handlert();
};

class cerr_message_handlert:public stream_message_handlert
{
public:
  // all messages go to stderr
  cerr_message_handlert();
};

class console_message_handlert : public message_handlert
{
public:
  void print(unsigned, const xmlt &) override
  {
  }

  void print(unsigned, const jsont &) override
  {
  }

  // level 4 and upwards go to cout, level 1-3 to cerr
  virtual void print(
    unsigned level,
    const std::string &message) override;

  virtual void flush(unsigned level) override;

  console_message_handlert() : console_message_handlert(false)
  {
  }

  explicit console_message_handlert(bool always_flush);

  std::string command(unsigned c) const override;

protected:
  const bool always_flush;

  /// true if we are outputting to a proper console
  bool is_a_tty;

  /// true if we use ECMA-48 SGR to render colors
  bool use_SGR;
};

#endif // CPROVER_UTIL_COUT_MESSAGE_H
