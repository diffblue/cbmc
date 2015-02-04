%{
// Strictly follows http://www.json.org/
%}

%{
#include "json_parser.h"

int yyjsonlex();
extern char *yyjsontext;

static irep_idt convert_TOK_STRING()
{
  assert(yyjsontext[0]=='"');
  std::size_t len=strlen(yyjsontext);
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
  
  // hash here
  return irep_idt(result);
}

static irep_idt convert_TOK_NUMBER()
{
  // hash here
  return irep_idt(yyjsontext);
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

object  : '{' { json_parser.push(irept()); } '}'
        | '{' { json_parser.push(irept()); } key_value_sequence '}'
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
          // we abuse the id to temporarily store the key
          json_parser.top().id(convert_TOK_STRING());
        }
          ':' value
        {
          irept tmp;
          json_parser.pop(tmp);
          json_parser.top().add(json_parser.top().id()).swap(tmp);
          json_parser.top().id(irep_idt()); // delete again
        }
        ;

array   : '[' { json_parser.push(irept()); } ']'
        | '[' { json_parser.push(irept()); } array_value_sequence ']'
        ;

array_value_sequence:
          array_value
        | array_value_sequence ',' array_value
        ;

array_value:
          value
        {
          irept tmp;
          json_parser.pop(tmp);
          json_parser.top().get_sub().push_back(tmp);
        }
        ;

value   : TOK_STRING
        { json_parser.push(irept(convert_TOK_STRING())); }
        | TOK_NUMBER
        { json_parser.push(irept(convert_TOK_NUMBER())); }
        | object
        | array
        | TOK_TRUE
        { json_parser.push(irept(ID_true)); }
        | TOK_FALSE
        { json_parser.push(irept(ID_false)); }
        | TOK_NULL
        { json_parser.push(irept(ID_null)); }
        ;

