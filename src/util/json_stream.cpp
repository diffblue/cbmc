/*******************************************************************\

Module:

Author: Peter Schrammel

\*******************************************************************/

#include "json_stream.h"

#include <ostream>

/// Output the element delimiter to the output stream
void json_streamt::output_delimiter()
{
  if(!first)
    out << ',';
  else
    first = false;
  out << '\n';
  out << std::string((indent + 1) * 2, ' ');
}

/// Construct a new JSON array stream
/// \param out: output stream
/// \param indent: indentation level
json_stream_arrayt::json_stream_arrayt(std::ostream &out, unsigned indent)
  : json_streamt(out, indent)
{
  out << '[';
}

/// Output the non-streaming JSON objects and closes the current child stream
void json_stream_arrayt::output_child_stream()
{
  if(!object.empty())
  {
    output_delimiter();
    object["array_element"].output_rec(out, indent + 1);
    object.clear();
  }
  if(child_stream)
  {
    child_stream->close();
    child_stream = nullptr;
  }
}

/// Output the finalizing character for a JSON array
void json_stream_arrayt::output_finalizer()
{
  out << '\n' << std::string(indent * 2, ' ');
  out << ']';
}

/// Constructor for json_stream_objectt.
/// \param out: The stream that is to be used to output the JSON object.
/// \param indent: Current indentation level.
json_stream_objectt::json_stream_objectt(std::ostream &out, unsigned indent)
  : json_streamt(out, indent)
{
  out << '{';
}

/// Create a new JSON array child stream.
json_stream_arrayt &json_streamt::create_child_stream_array()
{
  child_stream =
    std::unique_ptr<json_streamt>(new json_stream_arrayt(out, indent + 1));
  return static_cast<json_stream_arrayt &>(*child_stream);
}

/// Create a new JSON object child stream.
json_stream_objectt &json_streamt::create_child_stream_object()
{
  child_stream =
    std::unique_ptr<json_streamt>(new json_stream_objectt(out, indent + 1));
  return static_cast<json_stream_objectt &>(*child_stream);
}

/// Add a JSON object child stream
json_stream_objectt &json_stream_arrayt::push_back_stream_object()
{
  PRECONDITION(open);
  // To ensure consistency of the output, we flush and
  // close the current child stream before creating the new one.
  output_child_stream();
  output_delimiter();
  return create_child_stream_object();
}

/// Add a JSON array child stream
json_stream_arrayt &json_stream_arrayt::push_back_stream_array()
{
  PRECONDITION(open);
  // To ensure consistency of the output, we flush and
  // close the current child stream before creating the new one.
  output_child_stream();
  output_delimiter();
  return create_child_stream_array();
}

/// Add a JSON object stream for a specific key
/// \param key: key of the JSON property
json_stream_objectt &
json_stream_objectt::push_back_stream_object(const std::string &key)
{
  PRECONDITION(open);
  // To ensure consistency of the output, we flush and
  // close the current child stream before creating the new one.
  output_child_stream();
  output_delimiter();
  jsont::output_key(out, key);
  return create_child_stream_object();
}

/// Add a JSON array stream for a specific key
/// \param key: key of the JSON property
json_stream_arrayt &
json_stream_objectt::push_back_stream_array(const std::string &key)
{
  PRECONDITION(open);
  // To ensure consistency of the output, we flush and
  // close the current child stream before creating the new one.
  output_child_stream();
  output_delimiter();
  jsont::output_key(out, key);
  return create_child_stream_array();
}

/// Output non-streaming JSON properties and flushes and closes
/// the child stream
void json_stream_objectt::output_child_stream()
{
  for(const auto &obj : object)
  {
    output_delimiter();
    jsont::output_key(out, obj.first);
    obj.second.output_rec(out, indent + 1);
  }
  object.clear();
  if(child_stream)
  {
    child_stream->close();
    child_stream = nullptr;
  }
}

/// Output the finalizing character for a JSON object
void json_stream_objectt::output_finalizer()
{
  jsont::output_object(out, object, indent);
  out << '\n' << std::string(indent * 2, ' ');
  out << '}';
}
