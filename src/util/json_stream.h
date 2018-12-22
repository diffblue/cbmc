/*******************************************************************\

Module:

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_UTIL_JSON_STREAM_H
#define CPROVER_UTIL_JSON_STREAM_H

#include <iosfwd>
#include <memory>

#include "json.h"
#include "invariant.h"

class json_stream_objectt;
class json_stream_arrayt;

/// This class provides a facility for streaming JSON objects directly to the
/// output instead of waiting for the object to be fully formed in memory and
/// then print it (as done using `jsont`). This reduces memory consumption
/// when preparing e.g. large traces for output.
///
/// `json_streamt` is the base class from which the classes for streaming
/// arrays (`json_stream_arrayt`) and objects (`json_stream_objectt`) are
/// derived. `json_streamt` wraps an output stream and stores the current
/// element to be output. This can be either a child stream (of type
/// `json_streamt` that outputs JSON objects incrementally) or a
/// non-streaming JSON `object` (of type `jsont` that will be output as a
/// whole) To ensure consistency of the output, a class invariant is that
/// there is at most one child stream at any time. For this reason, the
/// existing child stream is flushed and closed when creating a new child
/// stream.
class json_streamt
{
public:
  /// Outputs the current current child stream and closes this JSON stream
  void close()
  {
    if(open)
    {
      output_child_stream();
      output_finalizer();
      open = false;
    }
  }

  virtual ~json_streamt() = default;

protected:
  /// Constructor to be used by derived classes
  /// \param _out: output stream
  /// \param _indent: indentation level
  json_streamt(std::ostream &_out, unsigned _indent)
    : open(true), out(_out), indent(_indent), first(true), child_stream(nullptr)
  {
  }

  /// Denotes whether the current stream is open or has been invalidated.
  bool open;
  std::ostream &out;
  unsigned indent;

  /// Is the current element the first element in the object or array?
  /// This is required to know whether a delimiter must be output or not.
  bool first;

  /// Non-streaming JSON elements
  /// These will be printed when closing the stream or creating a child stream.
  typedef std::map<std::string, jsont> objectt;
  objectt object;

  /// The current child stream. One can create and close many child streams
  /// sequentially (timewise), e.g. for each element in an array or each
  /// property in an object. The invariant is that there can only be at
  /// most child *one* stream at a time.
  std::unique_ptr<json_streamt> child_stream;
  json_stream_arrayt &create_child_stream_array();
  json_stream_objectt &create_child_stream_object();

  /// Outputs the delimiter between JSON elements
  void output_delimiter();

  // To be overridden by derived classes:
  virtual void output_child_stream() = 0;
  virtual void output_finalizer() = 0;
};

/// Provides methods for streaming JSON arrays
class json_stream_arrayt : public json_streamt
{
public:
  explicit json_stream_arrayt(std::ostream &out, unsigned indent = 0);

  /// Flushes and closes the stream on destruction
  ~json_stream_arrayt() override
  {
    close();
  }

  /// Push back a JSON element into the current array stream.
  /// Provided for compatibility with `jsont`.
  /// \param json: a non-streaming JSON element
  void push_back(const jsont &json)
  {
    PRECONDITION(open);
    // To ensure consistency of the output, we flush and
    // close the current child stream before printing the given element.
    output_child_stream();
    output_delimiter();
    json.output_rec(out, indent + 1);
  }

  /// Push back and return a new non-streaming JSON element into the current
  /// array stream.
  /// Provided for compatibility with `jsont`.
  /// \return a new empty, non-streaming JSON object
  jsont &push_back()
  {
    PRECONDITION(open);
    // To ensure consistency of the output, we flush and
    // close the current child stream before adding the given element.
    output_child_stream();
    // We store the new element in the object map.
    return object["array_element"];
  }

  json_stream_objectt &push_back_stream_object();
  json_stream_arrayt &push_back_stream_array();

protected:
  void output_child_stream() override;
  void output_finalizer() override;
};

/// Provides methods for streaming JSON objects
class json_stream_objectt : public json_streamt
{
public:
  explicit json_stream_objectt(std::ostream &out, unsigned indent = 0);

  /// Provide key-value lookup capabilities for the
  /// JSON object. Provided for compatibility with `jsont`.
  /// \param key: The key to be looked up inside the
  ///   attributes of the JSON object.
  jsont &operator[](const std::string &key)
  {
    return object[key];
  }

  ~json_stream_objectt() override
  {
    close();
  }

  /// Lookup the key of a non-streaming JSON element.
  /// \param key: The key to be looked up inside the
  ///   attributes of the JSON object.
  /// \return The value that corresponds to the key
  ///   if found, a null_json_object otherwise.
  const jsont &operator[](const std::string &key) const
  {
    objectt::const_iterator it = object.find(key);
    if(it == object.end())
      return jsont::null_json_object;
    else
      return it->second;
  }

  /// Push back a JSON element into the current object stream.
  /// Note the pushed key won't be available via operator[], as it has been
  /// output already.
  /// Provided for compatibility with `jsont`.
  /// \param key: new key to create in the streamed object
  /// \param json: a non-streaming JSON element
  void push_back(const std::string &key, const jsont &json)
  {
    PRECONDITION(open);
    // Check the key is not already due to be output later:
    PRECONDITION(!object.count(key));
    // To ensure consistency of the output, we flush and
    // close the current child stream before printing the given element.
    output_child_stream();
    output_delimiter();
    jsont::output_key(out, key);
    json.output_rec(out, indent + 1);
  }

  json_stream_objectt &push_back_stream_object(const std::string &key);
  json_stream_arrayt &push_back_stream_array(const std::string &key);

protected:
  void output_child_stream() override;
  void output_finalizer() override;
};

#endif // CPROVER_UTIL_JSON_STREAM_H
