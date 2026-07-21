#include <string>

// N5008 [lex.string]: a raw string literal R"(...)" ends only at the
// matching )" delimiter sequence; QUOTE characters inside the raw text
// are ordinary characters.  CBMC's lexer terminates the literal at
// the first inner quote, breaking every following token ("parse error
// before 'const std :: string'").  The shape of gdb_api.h's regex
// patterns, which blocks dog-fooding src/memory-analyzer/*.cpp.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  const std::string r_char = R"(\\"(\\\\[0-7]{3})\\")";
  const std::string r_string = R"((\\".*\\"))";
  __CPROVER_assert(r_string.size() == 10, "raw string content length");
  return 0;
}
