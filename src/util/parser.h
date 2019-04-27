/*******************************************************************\

Module: Parser utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Parser utilities

#ifndef CPROVER_UTIL_PARSER_H
#define CPROVER_UTIL_PARSER_H

#include <iosfwd>
#include <string>
#include <vector>

#include "expr.h"
#include "message.h"
#include "file_util.h"

class parsert:public messaget
{
public:
  std::istream *in;

  std::string this_line, last_line;

  std::vector<exprt> stack;

  virtual void clear()
  {
    line_no=0;
    previous_line_no=0;
    column=1;
    stack.clear();
    source_location.clear();
    last_line.clear();
  }

  parsert():in(nullptr) { clear(); }
  virtual ~parsert() { }

  // The following are for the benefit of the scanner

  bool read(char &ch)
  {
    if(!in->read(&ch, 1))
      return false;

    if(ch=='\n')
    {
      last_line.swap(this_line);
      this_line.clear();
    }
    else
      this_line+=ch;

    return true;
  }

  virtual bool parse()=0;

  bool eof()
  {
    return in->eof();
  }

  void parse_error(
    const std::string &message,
    const std::string &before);

  void inc_line_no()
  {
    ++line_no;
    column=1;
  }

  void set_line_no(unsigned _line_no)
  {
    line_no=_line_no;
  }

  void set_file(const irep_idt &file)
  {
    source_location.set_file(file);
    source_location.set_working_directory(
      get_current_working_directory());
  }

  irep_idt get_file() const
  {
    return source_location.get_file();
  }

  unsigned get_line_no() const
  {
    return line_no;
  }

  unsigned get_column() const
  {
    return column;
  }

  void set_column(unsigned _column)
  {
    column=_column;
  }

  void set_source_location(exprt &e)
  {
    // Only set line number when needed, as this destroys sharing.
    if(previous_line_no!=line_no)
    {
      previous_line_no=line_no;
      source_location.set_line(line_no);
    }

    e.add_source_location()=source_location;
  }

  void set_function(const irep_idt &function)
  {
    source_location.set_function(function);
  }

  void advance_column(unsigned token_width)
  {
    column+=token_width;
  }

protected:
  source_locationt source_location;
  unsigned line_no, previous_line_no;
  unsigned column;
};

exprt &_newstack(parsert &parser, unsigned &x);

#define newstack(x) _newstack(PARSER, (x))

#define parser_stack(x) (PARSER.stack[x])
#define stack_expr(x) (PARSER.stack[x])
#define stack_type(x) \
  (static_cast<typet &>(static_cast<irept &>(PARSER.stack[x])))

#define YY_INPUT(buf, result, max_size) \
    do { \
        for(result=0; result<max_size;) \
        { \
          char ch; \
          if(!PARSER.read(ch)) /* NOLINT(readability/braces) */ \
          { \
            if(result==0) \
              result=YY_NULL; \
            break; \
          } \
          \
          if(ch!='\r') /* NOLINT(readability/braces) */ \
          { \
            buf[result++]=ch; \
            if(ch=='\n') /* NOLINT(readability/braces) */ \
            { \
              PARSER.inc_line_no(); \
              break; \
            } \
          } \
        } \
    } while(0)

// The following tracks the column of the token, and is nicely explained here:
// http://oreilly.com/linux/excerpts/9780596155971/error-reporting-recovery.html

#define YY_USER_ACTION PARSER.advance_column(yyleng);

#endif // CPROVER_UTIL_PARSER_H
