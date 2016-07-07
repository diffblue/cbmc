/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MESSAGE_H
#define CPROVER_UTIL_MESSAGE_H

#include <string>
#include <iosfwd>
#include <sstream>

#include "source_location.h"

class message_handlert
{
public:
  message_handlert():verbosity(10), message_count(10, 0)
  {
  }

  virtual void print(unsigned level, const std::string &message) = 0;

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const source_locationt &location);

  virtual void flush(unsigned level)
  {
    // no-op by default
  }

  virtual ~message_handlert()
  {
  }

  void set_verbosity(unsigned _verbosity) { verbosity=_verbosity; }
  unsigned get_verbosity() const { return verbosity; }

  inline unsigned get_message_count(unsigned level) const
  {
    if(level>=message_count.size())
      return 0;

    return message_count[level];
  }

protected:
  unsigned verbosity;
  std::vector<unsigned> message_count;
};

class null_message_handlert:public message_handlert
{
public:
  virtual void print(unsigned level, const std::string &message)
  {
    message_handlert::print(level, message);
  }

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const source_locationt &location)
  {
    print(level, message);
  }
};

class stream_message_handlert:public message_handlert
{
public:
  explicit stream_message_handlert(std::ostream &_out):out(_out)
  {
  }

  virtual void print(unsigned level, const std::string &message)
  {
    message_handlert::print(level, message);

    if(verbosity>=level)
      out << message << '\n';
  }

  virtual void flush(unsigned level)
  {
    out << std::flush;
  }

protected:
  std::ostream &out;
};

class message_clientt
{
public:
  // Standard message levels:
  //
  //  0 none
  //  1 only errors
  //  2 + warnings
  //  4 + results
  //  6 + status/phase information
  //  8 + statistical information
  //  9 + progress information
  // 10 + debug info

  enum message_levelt
  {
    M_ERROR=1, M_WARNING=2, M_RESULT=4, M_STATUS=6,
    M_STATISTICS=8, M_PROGRESS=9, M_DEBUG=10
  };

  virtual ~message_clientt();

  virtual void set_message_handler(message_handlert &_message_handler);

  message_clientt():message_handler(NULL)
  {
  }

  explicit message_clientt(message_handlert &_message_handler):
    message_handler(&_message_handler)
  {
  }

  message_handlert &get_message_handler()
  {
    return *message_handler;
  }

protected:
  message_handlert *message_handler;
};

class messaget:public message_clientt
{
public:
  // constructors, destructor

  messaget():
    mstream(M_DEBUG, *this)
  {
  }

  messaget(const messaget &other):
    message_clientt(other),
    mstream(M_DEBUG, *this)
  {
  }

  explicit messaget(message_handlert &_message_handler):
    message_clientt(_message_handler),
    mstream(M_DEBUG, *this)
  {
  }

  virtual ~messaget() { }

  // old interface, will go away
  void status(
    const std::string &message,
    const std::string &file)
  {
    source_locationt location;
    location.set_file(file);
    print(6, message, -1, location);
  }

  void error(
    const std::string &message,
    const std::string &file)
  {
    source_locationt location;
    location.set_file(file);
    print(1, message, -1, location);
  }

  virtual void print(unsigned level, const std::string &message);

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number, // -1: no sequence information
    const source_locationt &location);

  // New interface

  class mstreamt:public std::ostringstream
  {
  public:
    mstreamt(
      unsigned _message_level,
      messaget &_message):
      message_level(_message_level),
      message(_message)
    {
    }

    unsigned message_level;
    messaget &message;
    source_locationt source_location;

    template <class T>
    mstreamt &operator << (const T &x)
    {
      static_cast<std::ostream &>(*this) << x;
      return *this;
    }

    // for feeding in manipulator functions such as eom
    mstreamt &operator << (mstreamt &(*func)(mstreamt &))
    {
      return func(*this);
    }
  };

  // Feeding 'eom' into the stream triggers
  // the printing of the message
  static inline mstreamt &eom(mstreamt &m)
  {
    if(m.message.message_handler)
    {
      m.message.message_handler->print(
        m.message_level,
        m.str(),
        -1,
        m.source_location);
      m.message.message_handler->flush(m.message_level);
    }
    m.clear(); // clears error bits
    m.str(std::string()); // clears the string
    m.source_location.clear();
    return m;
  }

  // in lieu of std::endl
  static inline mstreamt &endl(mstreamt &m)
  {
    static_cast<std::ostream &>(m) << std::endl;
    return m;
  }

  mstreamt &error()
  {
    mstream.message_level=M_ERROR;
    return mstream;
  }

  mstreamt &warning()
  {
    mstream.message_level=M_WARNING;
    return mstream;
  }

  mstreamt &result()
  {
    mstream.message_level=M_RESULT;
    return mstream;
  }

  mstreamt &status()
  {
    mstream.message_level=M_STATUS;
    return mstream;
  }

  mstreamt &statistics()
  {
    mstream.message_level=M_STATISTICS;
    return mstream;
  }

  mstreamt &progress()
  {
    mstream.message_level=M_PROGRESS;
    return mstream;
  }

  mstreamt &debug()
  {
    mstream.message_level=M_DEBUG;
    return mstream;
  }

  mstreamt &get_mstream(unsigned message_level)
  {
    mstream.message_level=message_level;
    return mstream;
  }

protected:
  mstreamt mstream;
};

#endif // CPROVER_UTIL_MESSAGE_H
