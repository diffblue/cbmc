#ifndef CPROVER_PARSER_H
#define CPROVER_PARSER_H

#include <iostream>
#include <string>
#include <vector>

#include "expr.h"
#include "message.h"

class parsert:public messaget
{
public:
  std::istream *in;
  irep_idt filename, function;
  
  unsigned line_no;
  std::string last_line;
  
  std::vector<exprt> stack;
  
  virtual void clear()
  {
    line_no=0;
    stack.clear();
    filename.clear();
    char_buffer.clear();
  }
  
  parsert() { clear(); }
  
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
    
  void set_location(exprt &e)
  {
    locationt &l=e.location();

    l.set_line(line_no);

    if(filename!=irep_idt())
      l.set_file(filename);
      
    if(function!=irep_idt())
      l.set_function(function);
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
    
    return in->read(&ch, 1);
  }
   
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
            if(ch=='\n') { PARSER.line_no++; break; } \
          } \
        } \
    } while(0)

#endif
