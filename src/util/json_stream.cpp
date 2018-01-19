/*******************************************************************\

Module:

Author: Peter Schrammel

\*******************************************************************/

#include "json_stream.h"

#include <ostream>

void json_streamt::output_delimiter()
{
  if(!first)
    out << ',';
  else
    first = false;
  out << '\n';
  out << std::string((indent+1)*2, ' ');
}

json_stream_arrayt::json_stream_arrayt(std::ostream &out, unsigned indent)
  : json_streamt(out, indent)
{
  out << '[';
}

void json_stream_arrayt::output_current()
{
  if(!object.empty())
  {
    output_delimiter();
    object[""].output_rec(out, indent+1);
    object.clear();
  }
  if(current)
  {
    current->close();
  }
}

void json_stream_arrayt::output_finalizer()
{
  out << '\n' << std::string(indent*2, ' ');
  out << ']';
}

json_stream_objectt::json_stream_objectt(std::ostream &out, unsigned indent)
  : json_streamt(out, indent)
{
  out << '{';
}

json_stream_arrayt &json_streamt::create_current_array()
{
  current =
    std::unique_ptr<json_streamt>(new json_stream_arrayt(out, indent + 1));
  return static_cast<json_stream_arrayt &>(*current);
}

json_stream_objectt &json_streamt::create_current_object()
{
  current =
    std::unique_ptr<json_streamt>(new json_stream_objectt(out, indent + 1));
  return static_cast<json_stream_objectt &>(*current);
}

json_stream_objectt &json_stream_arrayt::push_back_stream_object()
{
  PRECONDITION(open);
  output_current();
  output_delimiter();
  return create_current_object();
}

json_stream_arrayt &json_stream_arrayt::push_back_stream_array()
{
  PRECONDITION(open);
  output_current();
  output_delimiter();
  return create_current_array();
}

json_stream_objectt &json_stream_objectt::push_back_stream_object(const std::string &key)
{
  PRECONDITION(open);
  output_current();
  output_delimiter();
  jsont::output_key(out, key);
  return create_current_object();
}

json_stream_arrayt &json_stream_objectt::push_back_stream_array(const std::string &key)
{
  PRECONDITION(open);
  output_current();
  output_delimiter();
  jsont::output_key(out, key);
  return create_current_array();
}

void json_stream_objectt::output_current()
{
  for(const auto &obj : object)
  {
    output_delimiter();
    jsont::output_key(out, obj.first);
    obj.second.output_rec(out, indent+1);
  }
  object.clear();
  if(current)
  {
    current->close();
  }
}

void json_stream_objectt::output_finalizer()
{
  jsont::output_object(out, object, indent);
  out << '\n' << std::string(indent*2, ' ');
  out << '}';
}
