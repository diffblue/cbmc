/*******************************************************************\

Module: ostream_redactedt

Author: Diffblue

Date: Oct 2018

\*******************************************************************/

#ifndef CPROVER_UTIL_OSTREAM_REDACTEDT_H
#define CPROVER_UTIL_OSTREAM_REDACTEDT_H

#include <cstring>
#include <iostream>
#include <ostream>
#include <regex>
#include <sstream>
#include <string>

class ostream_redactedt : public std::ostringstream
{
private:
  // utility ostream and streambuf classes to enable sync with cin flushing - as happens for cout
  // this method of implmentation is required due to:
  // (ostream has non-virtual flush & no sync function,
  // only streambuf has a virtual sync() function
  class Sync_ostream : public std::ostream
  {
  private:
    class outbuf : public std::streambuf
    {
    private:
      int sync() override
      {
        parentstream->flush();
        return 0;
      };

    public:
      ostream_redactedt *parentstream;
    };
    outbuf syncbuffer;

  public:
    Sync_ostream() : std::ostream{&syncbuffer}
    {
    }

    void operator()(ostream_redactedt *parent)
    {
      syncbuffer.parentstream = parent;
    }
  };
  Sync_ostream sync_ostream;

public:
  ostream_redactedt(std::ostream &stream=std::cout, bool redact_on=true) :
    flush_output{&stream}, redact_on{redact_on}
  {
    sync_ostream(this);
    // sync with cin is non-essential, but nice to have the option to do so
    // when class is used as an alternative to std::cout
    // (this enables automatic output flush prior to cin, as is customary for
    // std::cout)
    std::cin.tie(get_sync_ostream());
  }

  ~ostream_redactedt()
  {
    flush();
  }

  Sync_ostream *get_sync_ostream()
  {
    return &sync_ostream;
  }

  template <typename T>
  void redact(const T &val){
    if (redact_on)
    {
      static_cast<std::ostream &>(*this)
        << redactstartTOKEN << val << redactendTOKEN;
    }else{
      static_cast<std::ostream &>(*this)<<val;
    }
  }

  template <typename T>
  ostream_redactedt &operator<<(const T &val)
  {
    redact(val);
    return *this;
  }

  // enable new line flushing behaviour ("\n")
  ostream_redactedt &operator<<(const char *str)
  {
    auto &sstemp = static_cast<std::ostream &>(*this);
    //C/ this if block forces each new line to be wrapped in redaction tokens
    if(strcmp("\n", str) == 0)
    {
      sstemp << str; // no need for redact tokens around a new line
    }
    else
    {
      redact(str);
    }
    return *this;
  }

  // enable new line flushing behaviour (single char, i.e. '\n')
  ostream_redactedt &operator<<(const char character)
  {
    auto &sstemp = static_cast<std::ostream &>(*this);

    if(character == '\n')
    {
      sstemp << character; // no need for redact tokens around a new line
    }
    else
    {
      redact(character);
    }
    return *this;
  }

  // std::endl support
  ostream_redactedt &operator<<(std::ostream &(*fp)(std::ostream &))
  {
    // detect std::endl and act accordingly
    if(fp == static_cast<std::ostream &(*)(std::ostream &)>(&std::endl))
    {
      static_cast<std::ostream &>(*this) << "\n";
      flush();
    }
    else
    {
      static_cast<std::ostream &>(*this) << fp;
    }
    return *this;
  }

  // std::hex et al support
  ostream_redactedt &operator<<(std::ios_base &(*fp)(std::ios_base &))
  {
    static_cast<std::ostream &>(*this) << fp;
    return *this;
  }

  std::string str()
  {
    // quite likely this method implementation can be optimised
    std::string sbufstring{std::ostringstream::str()};
    std::regex pattern(redactendTOKEN + redactstartTOKEN);
    sbufstring = std::regex_replace(sbufstring, pattern, "");

    // replace redaction tokens with user choice
    pattern = redactstartTOKEN;
    sbufstring = std::regex_replace(sbufstring, pattern, redactstart);
    pattern = redactendTOKEN;
    sbufstring = std::regex_replace(sbufstring, pattern, redactend);

    return sbufstring;
  }

  void str(std::string str)
  {
      std::ostringstream::str(str);
  }

  void flush()
  { // nb called upon destruction
    if (flush_output)
    {
      *flush_output << str();
      clear(); //clear any bad bits
      std::ostringstream::str("");
    }
  }

private:
  std::ostream *flush_output;

  std::string redactstartTOKEN{"_CPROVER_REDACT_ON_"};
  std::string redactendTOKEN{"_CPROVER_REDACT_OFF_"};

  std::string redactstart{"_<<<_"};
  std::string redactend{"_>>>_"};

  bool redact_on{true};
};

// ----------------------------------------------------------------------
class redact_off_nextt
{
public:
  redact_off_nextt(ostream_redactedt &message) : message{message}
  {
  }

  template <typename T>
  ostream_redactedt &operator<<(const T &val)
  {
    static_cast<std::ostringstream &>(message) << val;
    return message;
  }

  ostream_redactedt &message;
};

// NB redact_off_next.message is a reference, so no expensive copy involved
// here.
inline redact_off_nextt operator<<(
  redact_off_nextt redact_off_next,
  std::ios_base &(*fp)(std::ios_base &))
{
  static_cast<std::ostringstream &>(redact_off_next.message) << fp;
  return redact_off_nextt{redact_off_next.message};
}

// ----------------------------------------------
// function pointer as dummy variable
inline void redact_off_next(){}

inline redact_off_nextt operator<<(ostream_redactedt &message, void (*)())
{
  // Standard procedure would be to call the function pointer to return
  // an instance of the required type, overkill for this poc
  return redact_off_nextt{message};
}

// ----------------------------------------------------------------------
extern ostream_redactedt ostream_redacted_cout;
extern ostream_redactedt ostream_redact_off_cout;

extern ostream_redactedt ostream_redact_off_cout;
extern ostream_redactedt ostream_redact_off_cerr;

#endif //PROJECT_OSTREAM_REDACTEDT_H
