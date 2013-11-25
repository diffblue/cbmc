/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_MESSAGE_H

#define CPROVER_MESSAGE_H

#include <string>
#include <ostream>
#include <sstream>

#include "location.h"

class message_handlert
{
public:
  virtual void print(unsigned level, const std::string &message) = 0;

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const locationt &location);

  virtual ~message_handlert()
  {
  }
};
 
class null_message_handlert:public message_handlert
{
public:
  virtual void print(unsigned level, const std::string &message)
  {
  }

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const locationt &location)
  {
  }
};
 
class stream_message_handlert:public message_handlert
{
public:
  explicit inline stream_message_handlert(std::ostream &_out):out(_out)
  {
  }

  virtual void print(unsigned level, const std::string &message)
  { out << message << '\n'; }
  
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
    
  enum message_levelt { 
    M_ERROR=1, M_WARNING=2, M_RESULT=4, M_STATUS=6, M_STATISTICS=8, M_DEBUG=10
  };

  virtual ~message_clientt();

  virtual void set_message_handler(message_handlert &_message_handler);

  virtual void set_verbosity(unsigned _verbosity);
  virtual unsigned get_verbosity() const;
  
  inline message_clientt():
    verbosity(M_DEBUG), message_handler(NULL)
  {
  }
   
  inline explicit message_clientt(message_handlert &_message_handler):
    verbosity(M_DEBUG), message_handler(&_message_handler)
  {
  }
   
  inline message_handlert &get_message_handler()
  {
    return *message_handler;
  }

protected:
  unsigned verbosity;
  message_handlert *message_handler;
};

class messaget:public message_clientt
{
public:
  // constructors, destructor
  
  inline messaget():
    mstream(M_DEBUG, verbosity, &message_handler)
  {
  }
  
  inline messaget(const messaget &other):
    message_clientt(other),
    mstream(M_DEBUG, verbosity, &message_handler)
  {
  }
   
  inline explicit messaget(message_handlert &_message_handler):
    message_clientt(_message_handler),
    mstream(M_DEBUG, verbosity, &message_handler)
  {
  }
   
  virtual ~messaget() { }
  
  // old interface, will go away

  inline void print(const std::string &message)
  { print(1, message); }

  inline void status(const std::string &message)
  { print(6, message); }
  
  inline void result(const std::string &message)
  { print(4, message); }
   
  inline void warning(const std::string &message)
  { print(2, message); }
   
  inline void debug(const std::string &message)
  { print(9, message); }
   
  inline void status(
    const std::string &message,
    const std::string &file)
  {
    locationt location;
    location.set_file(file);
    print(6, message, -1, location);
  }
   
  inline void error(const std::string &message)
  { print(1, message); }

  inline void statistics(const std::string &message)
  { print(8, message); }

  inline void error(
    const std::string &message,
    const std::string &file)
  {
    locationt location;
    location.set_file(file);
    print(1, message, -1, location);
  }

  virtual void print(unsigned level, const std::string &message);

  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number, // -1: no sequence information
    const locationt &location);
  
  // New interface
  
  class mstreamt:public std::ostringstream
  {
  public:
    inline mstreamt(
      unsigned _message_level,
      unsigned _verbosity,
      message_handlert **_message_handler):
      message_level(_message_level),
      message_handler(_message_handler)
    {
    }

    unsigned message_level, verbosity;
    message_handlert **message_handler;

    template <class T>
    inline mstreamt &operator << (const T &x)
    {
      static_cast<std::ostream &>(*this) << x;
      return *this;
    }

    // for feeding in manipulator functions such as eom
    inline mstreamt &operator << (mstreamt &(*func)(mstreamt &))
    {
      return func(*this);
    }
  };

  // Feeding 'eom' into the stream triggers
  // the printing of the message
  static inline mstreamt &eom(mstreamt &m)
  {
    if((*m.message_handler)!=NULL && m.verbosity>=m.message_level)
      (*m.message_handler)->print(m.message_level, m.str());
    m.clear(); // clears error bits
    m.str(std::string()); // clears the string
    return m;
  }

  // in lieu of std::endl
  static inline mstreamt &endl(mstreamt &m)
  {
    static_cast<std::ostream &>(m) << std::endl;
    return m;
  }
  
  inline mstreamt &error()
  {
    mstream.message_level=M_ERROR;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
  inline mstreamt &warning()
  {
    mstream.message_level=M_WARNING;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
  inline mstreamt &result()
  {
    mstream.message_level=M_RESULT;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
  inline mstreamt &status()
  {
    mstream.message_level=M_STATUS;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
  inline mstreamt &statistics()
  {
    mstream.message_level=M_STATISTICS;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
  inline mstreamt &debug()
  {
    mstream.message_level=M_DEBUG;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
  inline mstreamt &get_mstream(unsigned message_level)
  {
    mstream.message_level=message_level;
    mstream.verbosity=verbosity;
    return mstream;
  }
  
protected:
  mstreamt mstream;
};

#endif
