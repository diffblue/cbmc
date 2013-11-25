#ifndef CPROVER_PARSER_H
#define CPROVER_PARSER_H

#include <istream>
#include <string>
#include <vector>

#include "expr.h"
#include "message.h"

class parsert:public messaget
{
public:
  std::istream *in;
  locationt location;
  
  std::string last_line;
  
  std::vector<exprt> stack;
  
  virtual void clear()
  {
    line_no=0;
    stack.clear();
    location.clear();
    char_buffer.clear();
  }
  
  inline parsert() { clear(); }
  
  virtual ~parsert() { }

  virtual bool read(char &ch)
  {
    if(!read2(ch)) return false;

    if(ch=='\n')
      last_line="";
    else
      last_line+=ch;
    
    return true;
  }
   
  virtual bool parse()
  {
    return true;
  }
   
  virtual bool peek(char &ch)
  {
    if(!char_buffer.empty())
    {
      ch=char_buffer.front();
      return true;
    }
    
    if(!in->read(&ch, 1)) 
      return false;
     
    char_buffer.push_back(ch);
    return true;
  }
  
  virtual bool eof()
  {
    return char_buffer.empty() && in->eof();
  }
  
  void parse_error(
    const std::string &message,
    const std::string &before);
    
  void inc_line_no()
  {
    ++line_no;
    location.set_line(line_no);
  }
  
  void set_line_no(unsigned _line_no)
  {
    line_no=_line_no;
    location.set_line(line_no);
  }
  
  inline void set_file(const irep_idt &file)
  {
    location.set_file(file);
  }
  
  inline unsigned get_line_no() const
  {
    return line_no;
  }

  inline void set_location(exprt &e)
  {
    e.location()=location;
  }

private:
  virtual bool read2(char &ch)
  {
    if(!char_buffer.empty())
    {
      ch=char_buffer.front();
      char_buffer.pop_front();
      return true;
    }
    
    return in->read(&ch, 1)!=0;
  }
   
  unsigned line_no;
  std::list<char> char_buffer;
};
 
exprt &_newstack(parsert &parser, unsigned &x);

#define newstack(x) _newstack(PARSER, (x))

#define stack(x) (PARSER.stack[x])

#define YY_INPUT(buf,result,max_size) \
    do { \
        for(result=0; result<max_size;) \
        { \
          char ch; \
          if(!PARSER.read(ch)) \
          { \
            if(result==0) result=YY_NULL; \
            break; \
          } \
          \
          if(ch!='\r') \
          { \
            buf[result++]=ch; \
            if(ch=='\n') { PARSER.inc_line_no(); break; } \
          } \
        } \
    } while(0)

#endif
