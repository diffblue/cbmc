%{
// Strictly follows http://www.json.org/
%}

%{
#include "json_parser.h"

int yyjsonlex();
extern char *yyjsontext;
extern std::size_t yyjsonleng;

static std::string convert_TOK_STRING()
{
  assert(yyjsontext[0]=='"');
  std::size_t len=yyjsonleng;
  assert(len>=2);
  assert(yyjsontext[len-1]=='"');
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
        break;
        
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

%token	TOK_STRING
%token	TOK_NUMBER
%token	TOK_TRUE
%token	TOK_FALSE
%token	TOK_NULL

%%

document: value
        ;

object  : '{' { json_parser.push(jsont::json_object()); } '}'
        | '{' { json_parser.push(jsont::json_object()); } key_value_sequence '}'
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
          json_parser.top().object[json_parser.top().value].swap(tmp);
          json_parser.top().value.clear(); // end abuse
        }
        ;

array   : '[' { json_parser.push(jsont::json_array()); } ']'
        | '[' { json_parser.push(jsont::json_array()); } array_value_sequence ']'
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
          json_parser.top().array.push_back(tmp);
        }
        ;

value   : TOK_STRING
        { json_parser.push(jsont::json_string(convert_TOK_STRING())); }
        | TOK_NUMBER
        { json_parser.push(jsont::json_number(convert_TOK_NUMBER())); }
        | object
        | array
        | TOK_TRUE
        { json_parser.push(jsont::json_true()); }
        | TOK_FALSE
        { json_parser.push(jsont::json_false()); }
        | TOK_NULL
        { json_parser.push(jsont::json_null()); }
        ;

