/*******************************************************************\

Module: util

Author: Diffblue Ltd.

\*******************************************************************/

#include "unwrap_nested_exception.h"
#include "invariant.h"
#include "string_utils.h"
#include "suffix.h"
#include "throw_with_nested.h"

#include <sstream>
#include <vector>

/// Given a potentially nested exception, produce a string with all of nested
/// exceptions information. If a nested exception string contains new lines
/// then the newlines are indented to the correct level.
/// \param e: The outer exeception
/// \param level: How many exceptions have already been unrolled
/// \return A string with all nested exceptions printed and indented
std::string unwrap_exception(const std::exception &e, int level)
{
  const std::string msg = e.what();
  std::vector<std::string> lines =
    split_string(msg, '\n', false, true);
  std::ostringstream message_stream;
  message_stream << std::string(level, ' ') << "exception: ";
  join_strings(
    message_stream, lines.begin(), lines.end(), "\n" + std::string(level, ' '));

  try
  {
    util_rethrow_if_nested(e);
  }
  catch(const std::exception &e)
  {
    std::string nested_message = unwrap_exception(e, level + 1);
    // Some exception messages already end in a new line (e.g. as they have
    // dumped an irept. Most do not so add a new line on.
    if(nested_message.back() != '\n')
    {
      message_stream << '\n';
    }
    message_stream << nested_message;
  }
  catch(...)
  {
    UNREACHABLE;
  }
  return message_stream.str();
}
