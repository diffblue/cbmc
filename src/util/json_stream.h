/*******************************************************************\

Module:

Author: Peter Schrammel

\*******************************************************************/


#ifndef CPROVER_UTIL_JSON_STREAM_H
#define CPROVER_UTIL_JSON_STREAM_H

#include <memory>

#include "json.h"
#include "invariant.h"

class json_stream_objectt;
class json_stream_arrayt;

class json_streamt
{
public:
  void close()
  {
    if(open)
    {
      output_current();
      output_finalizer();
      open = false;
    }
  }

protected:
  json_streamt(std::ostream &_out, unsigned _indent)
    : open(true), out(_out), indent(_indent), first(true), current(nullptr)
  {
  }

  bool open;
  std::ostream &out;

  unsigned indent;
  bool first;

  typedef std::map<std::string, jsont> objectt;
  objectt object;

  std::unique_ptr<json_streamt> current;
  json_stream_arrayt &create_current_array();
  json_stream_objectt &create_current_object();

  void output_delimiter();

  virtual void output_current()
  {
    // no-op
  }

  virtual void output_finalizer()
  {
    // no-op
  }
};

class json_stream_arrayt:public json_streamt
{
public:
  explicit json_stream_arrayt(std::ostream &out, unsigned indent=0);

  ~json_stream_arrayt()
  {
    close();
  }

  void push_back(const jsont &json)
  {
    PRECONDITION(open);
    output_current();
    output_delimiter();
    json.output_rec(out, indent+1);
  }

  jsont &push_back()
  {
    PRECONDITION(open);
    output_current();
    return object[""];
  }

  json_stream_objectt &push_back_stream_object();
  json_stream_arrayt &push_back_stream_array();

protected:
  void output_current() override;
  void output_finalizer() override;
};

class json_stream_objectt:public json_streamt
{
public:
  explicit json_stream_objectt(std::ostream &out, unsigned indent=0);

  jsont &operator[](const std::string &key)
  {
    return object[key];
  }

  ~json_stream_objectt()
  {
    close();
  }

  const jsont &operator[](const std::string &key) const
  {
    objectt::const_iterator it=object.find(key);
    if(it==object.end())
      return jsont::null_json_object;
    else
      return it->second;
  }

  json_stream_objectt &push_back_stream_object(const std::string &key);
  json_stream_arrayt &push_back_stream_array(const std::string &key);

protected:
  void output_current() override;
  void output_finalizer() override;
};

#endif // CPROVER_UTIL_JSON_STREAM_H
