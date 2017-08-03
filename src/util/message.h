/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MESSAGE_H
#define CPROVER_UTIL_MESSAGE_H

#include <string>
#include <iosfwd>
#include <sstream>

#include "invariant.h"
#include "source_location.h"

class message_handlert
{
public:
  message_handlert():verbosity(10), message_count(10, 0)
  {
  }

  virtual void print(
    unsigned level,
    const std::string &message,
    bool preformatted) = 0;

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const source_locationt &location,
    bool preformatted);

  virtual void flush(unsigned level)
  {
    // no-op by default
  }

  virtual ~message_handlert()
  {
  }

  void set_verbosity(unsigned _verbosity) { verbosity=_verbosity; }
  unsigned get_verbosity() const { return verbosity; }

  unsigned get_message_count(unsigned level) const
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
  virtual void print(
    unsigned level,
    const std::string &message,
    bool preformatted)
  {
    message_handlert::print(level, message, preformatted);
  }

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const source_locationt &location,
    bool preformatted)
  {
    print(level, message, preformatted);
  }
};

class stream_message_handlert:public message_handlert
{
public:
  explicit stream_message_handlert(std::ostream &_out):out(_out)
  {
  }

  virtual void print(
    unsigned level,
    const std::string &message,
    bool preformatted)
  {
    message_handlert::print(level, message, preformatted);

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

class messaget
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

  virtual void set_message_handler(message_handlert &_message_handler)
  {
    message_handler=&_message_handler;
  }

  message_handlert &get_message_handler()
  {
    INVARIANT(message_handler!=nullptr, "message handler is set");
    return *message_handler;
  }

  // constructors, destructor

  messaget():
    message_handler(nullptr),
    mstream(M_DEBUG, *this)
  {
  }

  messaget(const messaget &other):
    message_handler(other.message_handler),
    mstream(other.mstream)
  {
  }

  explicit messaget(message_handlert &_message_handler):
    message_handler(&_message_handler),
    mstream(M_DEBUG, *this)
  {
  }

  virtual ~messaget();

  class mstreamt:public std::ostringstream
  {
  public:
    mstreamt(
      unsigned _message_level,
      messaget &_message):
      message_level(_message_level),
      message(_message),
      preformatted(false)
    {
    }

    mstreamt(const mstreamt &other):
      message_level(other.message_level),
      message(other.message),
      source_location(other.source_location),
      preformatted(false)
    {
    }

    unsigned message_level;
    messaget &message;
    source_locationt source_location;
    bool preformatted;

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
  static mstreamt &eom(mstreamt &m)
  {
    if(m.message.message_handler)
    {
      m.message.message_handler->print(
        m.message_level,
        m.str(),
        -1,
        m.source_location,
        m.preformatted);
      m.message.message_handler->flush(m.message_level);
    }
    m.preformatted=false;
    m.clear(); // clears error bits
    m.str(std::string()); // clears the string
    m.source_location.clear();
    return m;
  }

  static mstreamt &preformatted_output(mstreamt &m)
  {
    m.preformatted=true;
    return m;
  }

  // in lieu of std::endl
  static mstreamt &endl(mstreamt &m)
  {
    static_cast<std::ostream &>(m) << std::endl;
    return m;
  }

  mstreamt &get_mstream(unsigned message_level)
  {
    mstream.message_level=message_level;
    return mstream;
  }

  mstreamt &error()
  {
    return get_mstream(M_ERROR);
  }

  mstreamt &warning()
  {
    return get_mstream(M_WARNING);
  }

  mstreamt &result()
  {
    return get_mstream(M_RESULT);
  }

  mstreamt &status()
  {
    return get_mstream(M_STATUS);
  }

  mstreamt &statistics()
  {
    return get_mstream(M_STATISTICS);
  }

  mstreamt &progress()
  {
    return get_mstream(M_PROGRESS);
  }

  mstreamt &debug()
  {
    return get_mstream(M_DEBUG);
  }

protected:
  message_handlert *message_handler;
  mstreamt mstream;
};

#endif // CPROVER_UTIL_MESSAGE_H
