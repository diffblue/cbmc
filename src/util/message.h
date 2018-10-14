/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MESSAGE_H
#define CPROVER_UTIL_MESSAGE_H

#include <functional>
#include <iosfwd>
#include <sstream>
#include <string>

#include "invariant.h"
#include "json.h"
#include "source_location.h"

class xmlt;

class message_handlert
{
public:
  message_handlert():verbosity(10), message_count(10, 0)
  {
  }

  virtual void print(unsigned level, const std::string &message)=0;

  virtual void print(unsigned level, const xmlt &xml)
  {
    // no-op by default
  }

  virtual void print(unsigned level, const jsont &json)
  {
    // no-op by default
  }

  virtual void print(
    unsigned level,
    const std::string &message,
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

  std::size_t get_message_count(unsigned level) const
  {
    if(level>=message_count.size())
      return 0;

    return message_count[level];
  }

  /// \brief Create an ECMA-48 SGR (Select Graphic Rendition) command.
  /// The default behavior is no action.
  virtual std::string command(unsigned) const
  {
    return std::string();
  }

protected:
  unsigned verbosity;
  std::vector<std::size_t> message_count;
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
    const source_locationt &)
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

  static unsigned eval_verbosity(
    const std::string &user_input,
    const message_levelt default_verbosity,
    message_handlert &dest);

  virtual void set_message_handler(message_handlert &_message_handler)
  {
    message_handler=&_message_handler;
  }

  message_handlert &get_message_handler()
  {
    INVARIANT(
      message_handler!=nullptr,
      "message handler should be set before calling get_message_handler");
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
    mstream(other.mstream, *this)
  {
  }

  messaget &operator=(const messaget &other)
  {
    message_handler=other.message_handler;
    mstream.assign_from(other.mstream);
    return *this;
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
      message(_message)
    {
    }

    mstreamt(const mstreamt &other)=delete;

    mstreamt(const mstreamt &other, messaget &_message):
      message_level(other.message_level),
      message(_message),
      source_location(other.source_location)
    {
    }

    mstreamt &operator=(const mstreamt &other)=delete;

    unsigned message_level;
    messaget &message;
    source_locationt source_location;

    mstreamt &operator << (const xmlt &data)
    {
      if(this->tellp() > 0)
        *this << eom; // force end of previous message
      if(message.message_handler)
      {
        message.message_handler->print(message_level, data);
      }
      return *this;
    }

    mstreamt &operator << (const json_objectt &data)
    {
      if(this->tellp() > 0)
        *this << eom; // force end of previous message
      if(message.message_handler)
      {
        message.message_handler->print(message_level, data);
      }
      return *this;
    }

    template <class T>
    mstreamt &operator << (const T &x)
    {
      static_cast<std::ostream &>(*this) << x;
      return *this;
    }

  private:
    void assign_from(const mstreamt &other)
    {
      message_level=other.message_level;
      source_location=other.source_location;
      // message, the pointer to my enclosing messaget, remains unaltered.
    }

    friend class messaget;
  };

  // Feeding 'eom' into the stream triggers the printing of the message
  // This is implemented as an I/O manipulator (compare to STL's endl).
  class eomt
  {
  };

  static eomt eom;

  friend mstreamt &operator<<(mstreamt &m, eomt)
  {
    if(m.message.message_handler)
    {
      m.message.message_handler->print(
        m.message_level,
        m.str(),
        m.source_location);
      m.message.message_handler->flush(m.message_level);
    }
    m.clear(); // clears error bits
    m.str(std::string()); // clears the string
    m.source_location.clear();
    return m;
  }

  // This is an I/O manipulator (compare to STL's set_precision).
  class commandt
  {
  public:
    explicit commandt(unsigned _command) : command(_command)
    {
    }

    unsigned command;
  };

  /// feed a command into an mstreamt
  friend mstreamt &operator<<(mstreamt &m, const commandt &c)
  {
    if(m.message.message_handler)
      return m << m.message.message_handler->command(c.command);
    else
      return m;
  }

  /// \brief Create an ECMA-48 SGR (Select Graphic Rendition) command.
  static commandt command(unsigned c)
  {
    return commandt(c);
  }

  /// return to default formatting,
  /// as defined by the terminal
  static commandt reset()
  {
    return command(0);
  }

  /// render text with red foreground color
  static commandt red()
  {
    return command(31);
  }

  /// render text with green foreground color
  static commandt green()
  {
    return command(32);
  }

  /// render text with yellow foreground color
  static commandt yellow()
  {
    return command(33);
  }

  /// render text with blue foreground color
  static commandt blue()
  {
    return command(34);
  }

  /// render text with bold font
  static commandt bold()
  {
    return command(1);
  }

  mstreamt &get_mstream(unsigned message_level) const
  {
    mstream.message_level=message_level;
    return mstream;
  }

  mstreamt &error() const
  {
    return get_mstream(M_ERROR);
  }

  mstreamt &warning() const
  {
    return get_mstream(M_WARNING);
  }

  mstreamt &result() const
  {
    return get_mstream(M_RESULT);
  }

  mstreamt &status() const
  {
    return get_mstream(M_STATUS);
  }

  mstreamt &statistics() const
  {
    return get_mstream(M_STATISTICS);
  }

  mstreamt &progress() const
  {
    return get_mstream(M_PROGRESS);
  }

  mstreamt &debug() const
  {
    return get_mstream(M_DEBUG);
  }

  void conditional_output(
    mstreamt &mstream,
    const std::function<void(mstreamt &)> &output_generator) const;

protected:
  message_handlert *message_handler;
  mutable mstreamt mstream;
};

#endif // CPROVER_UTIL_MESSAGE_H
