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

int yyjsonlex(void *);
char *yyjsonget_text(void *);
#define yyjsontext yyjsonget_text(scanner)
int yyjsonget_leng(void *); // really an int, not a size_t
#define yyjsonleng yyjsonget_leng(scanner)

static std::string convert_JTOK_STRING(void *scanner)
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

static std::string convert_JTOK_NUMBER(void *scanner)
{
  return yyjsontext;
}

int yyjsonerror(json_parsert &json_parser, void *scanner, const std::string &error)
{
  json_parser.parse_error(error, yyjsontext);
  return 0;
}

%}

%parse-param {json_parsert &json_parser}
%parse-param {void *scanner}
%lex-param {void *scanner}

%token JTOK_STRING
%token JTOK_NUMBER
%token JTOK_TRUE
%token JTOK_FALSE
%token JTOK_NULL

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
          JTOK_STRING
        {
          // we abuse the 'value' to temporarily store the key
          json_parser.top().value=convert_JTOK_STRING(scanner);
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

value   : JTOK_STRING
        { json_parser.push(json_stringt(convert_JTOK_STRING(scanner))); }
        | JTOK_NUMBER
        { json_parser.push(json_numbert(convert_JTOK_NUMBER(scanner))); }
        | object
        | array
        | JTOK_TRUE
        { json_parser.push(json_truet()); }
        | JTOK_FALSE
        { json_parser.push(json_falset()); }
        | JTOK_NULL
        { json_parser.push(json_nullt()); }
        ;

