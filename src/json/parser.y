%{
#ifdef _MSC_VER
// possible loss of data
#pragma warning(disable:4242)
// possible loss of data
#pragma warning(disable:4244)
// signed/unsigned mismatch
#pragma warning(disable:4365)
// switch with default but no case labels
#pragma warning(disable:4065)
// unreachable code
#pragma warning(disable:4702)
#endif

// Strictly follows http://www.json.org/
%}

%{
#include "json_parser.h"

#include <util/unicode.h>

int yyjsonlex();
extern char *yyjsontext;
extern int yyjsonleng; // really an int, not a size_t

static std::string convert_TOK_STRING()
{
  PRECONDITION(yyjsontext[0]=='"');
  std::size_t len=yyjsonleng;
  PRECONDITION(len>=2);
  PRECONDITION(yyjsontext[len-1]=='"');
  std::string result;
  result.reserve(len);
  for(char *p=yyjsontext+1; *p!='"' && *p!=0; p++)
  {
    if(*p=='\\')
    {
      p++;
      switch(*p)
      {
      case '"':  result+='"'; break;
      case '\\': result+='\\'; break;
      case '/':  result+='/'; break;
      case 'b':  result+='\b'; break;
      case 'f':  result+='\f'; break;
      case 'n':  result+='\n'; break;
      case 'r':  result+='\r'; break;
      case 't':  result+='\t'; break;
      case 'u':
      {
        // Character in hexadecimal Unicode representation, in the format
        // \uABCD, i.e. the following four digits are part of this character.
        char *last_hex_digit = p + 4;
        INVARIANT(
          last_hex_digit < yyjsontext + len - 1,
          "all digits are in bounds");
        std::string hex(++p, 4);
        result += codepoint_hex_to_utf8(hex);
        p = last_hex_digit;
        break;
      }
      default:; /* an error */
      }
    }
    else
      result+=*p;
  }
  
  return result;
}

static std::string convert_TOK_NUMBER()
{
  return yyjsontext;
}

int yyjsonerror(const std::string &error)
{
  json_parser.parse_error(error, yyjsontext);
  return 0;
}

%}

%token TOK_STRING
%token TOK_NUMBER
%token TOK_TRUE
%token TOK_FALSE
%token TOK_NULL

%%

document: value
        ;

object  : '{' { json_parser.push(json_objectt()); } '}'
        | '{' { json_parser.push(json_objectt()); } key_value_sequence '}'
        ;

key_value_sequence:
          key_value_pair
        | key_value_sequence ',' key_value_pair
        {
        }
        ;
        
key_value_pair:
          TOK_STRING
        {
          // we abuse the 'value' to temporarily store the key
          json_parser.top().value=convert_TOK_STRING();
        }
          ':' value
        {
          jsont tmp;
          json_parser.pop(tmp);
          to_json_object(json_parser.top())[json_parser.top().value].swap(tmp);
          json_parser.top().value.clear(); // end abuse
        }
        ;

array   : '[' { json_parser.push(json_arrayt()); } ']'
        | '[' { json_parser.push(json_arrayt()); } array_value_sequence ']'
        ;

array_value_sequence:
          array_value
        | array_value_sequence ',' array_value
        ;

array_value:
          value
        {
          jsont tmp;
          json_parser.pop(tmp);
          to_json_array(json_parser.top()).push_back(tmp);
        }
        ;

value   : TOK_STRING
        { json_parser.push(json_stringt(convert_TOK_STRING())); }
        | TOK_NUMBER
        { json_parser.push(json_numbert(convert_TOK_NUMBER())); }
        | object
        | array
        | TOK_TRUE
        { json_parser.push(json_truet()); }
        | TOK_FALSE
        { json_parser.push(json_falset()); }
        | TOK_NULL
        { json_parser.push(json_nullt()); }
        ;

