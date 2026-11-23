/*******************************************************************\

Module: Inline assembly: splitting templates into instructions

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Splitting the template of an inline assembly statement into instructions

#include "asm_template.h"

#include "asm_operands.h"

#include <algorithm>
#include <cctype>

static bool is_identifier_start(char c, const asm_syntaxt &syntax)
{
  return std::isalpha(static_cast<unsigned char>(c)) || c == '_' || c == '.' ||
         syntax.identifier_characters.find(c) != std::string::npos;
}

static bool is_identifier_char(char c, const asm_syntaxt &syntax)
{
  return is_identifier_start(c, syntax) ||
         std::isdigit(static_cast<unsigned char>(c));
}

static std::string to_lower(std::string s)
{
  std::transform(
    s.begin(),
    s.end(),
    s.begin(),
    [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
  return s;
}

/// Remove `/* ... */` comments and line comments, and split into statements
static std::vector<std::string>
split_statements(const std::string &text, const asm_syntaxt &syntax)
{
  std::vector<std::string> result;
  std::string current;
  bool in_string = false;

  for(std::size_t i = 0; i < text.size(); ++i)
  {
    const char c = text[i];

    if(in_string)
    {
      current += c;
      if(c == '\\' && i + 1 < text.size())
        current += text[++i];
      else if(c == '"')
        in_string = false;
      continue;
    }

    if(c == '"')
    {
      in_string = true;
      current += c;
      continue;
    }

    if(c == '/' && i + 1 < text.size() && text[i + 1] == '*')
    {
      const auto end = text.find("*/", i + 2);
      i = end == std::string::npos ? text.size() : end + 1;
      current += ' ';
      continue;
    }

    bool comment = false;
    for(const auto &marker : syntax.line_comments)
    {
      if(text.compare(i, marker.size(), marker) == 0)
      {
        comment = true;
        break;
      }
    }

    if(comment)
    {
      const auto end = text.find('\n', i);
      i = end == std::string::npos ? text.size() : end - 1;
      continue;
    }

    if(c == '\n' || syntax.separators.find(c) != std::string::npos)
    {
      result.push_back(current);
      current.clear();
      continue;
    }

    current += c;
  }

  result.push_back(current);
  return result;
}

/// Tokenize one statement, resolving `%` references
static bool tokenize(
  const std::string &text,
  const asm_syntaxt &syntax,
  const asm_operandst *operands,
  asm_token_listt &tokens,
  std::string &error)
{
  std::size_t i = 0;
  while(i < text.size())
  {
    const char c = text[i];

    if(std::isspace(static_cast<unsigned char>(c)))
    {
      ++i;
      continue;
    }

    if(c == '%' && operands != nullptr)
    {
      ++i;
      if(
        i < text.size() &&
        (text[i] == '%' || text[i] == '|' || text[i] == '{' || text[i] == '}'))
      {
        // %% is a literal %; %|, %{, %} are dialect markers
        if(text[i] == '%')
          tokens.push_back({asm_tokent::kindt::PUNCTUATION, "%"});
        ++i;
        continue;
      }

      if(i < text.size() && text[i] == '=')
      {
        // a number unique to this instance of the statement
        asm_tokent token{asm_tokent::kindt::NUMBER, "0"};
        tokens.push_back(token);
        ++i;
        continue;
      }

      std::string modifier;
      while(i < text.size() &&
            std::isalpha(static_cast<unsigned char>(text[i])))
        modifier += text[i++];

      asm_tokent token{asm_tokent::kindt::OPERAND, ""};
      token.modifier = modifier;

      if(i < text.size() && text[i] == '[')
      {
        const auto end = text.find(']', i);
        if(end == std::string::npos)
        {
          error = "unterminated operand name";
          return false;
        }
        const std::string name = text.substr(i + 1, end - i - 1);
        i = end + 1;

        if(modifier == "l")
        {
          const auto label = operands->find_label(name);
          if(!label.has_value())
          {
            error = "unknown label %l[" + name + "]";
            return false;
          }
          token.kind = asm_tokent::kindt::C_LABEL;
          token.index = *label;
          token.modifier.clear();
        }
        else
        {
          const auto index = operands->find(name);
          if(!index.has_value())
          {
            error = "unknown operand %[" + name + "]";
            return false;
          }
          token.index = *index;
        }
      }
      else if(
        i < text.size() && std::isdigit(static_cast<unsigned char>(text[i])))
      {
        std::size_t index = 0;
        while(i < text.size() &&
              std::isdigit(static_cast<unsigned char>(text[i])))
          index = index * 10 + static_cast<std::size_t>(text[i++] - '0');

        if(modifier == "l")
        {
          if(
            index < operands->operands.size() ||
            index >= operands->operands.size() + operands->labels.size())
          {
            error =
              "label reference %l" + std::to_string(index) + " out of range";
            return false;
          }
          token.kind = asm_tokent::kindt::C_LABEL;
          token.index = index - operands->operands.size();
          token.modifier.clear();
        }
        else if(index >= operands->operands.size())
        {
          error =
            "operand reference %" + std::to_string(index) + " out of range";
          return false;
        }
        else
          token.index = index;
      }
      else
      {
        error = "unsupported % sequence";
        return false;
      }

      tokens.push_back(token);
      continue;
    }

    if(std::isdigit(static_cast<unsigned char>(c)))
    {
      std::size_t start = i;
      bool hex = false;
      if(
        c == '0' && i + 1 < text.size() &&
        (text[i + 1] == 'x' || text[i + 1] == 'X'))
      {
        hex = true;
        i += 2;
        while(i < text.size() &&
              std::isxdigit(static_cast<unsigned char>(text[i])))
          ++i;
      }
      else
      {
        while(i < text.size() &&
              std::isdigit(static_cast<unsigned char>(text[i])))
          ++i;
      }

      const std::string digits = text.substr(start, i - start);

      // GNU local label references: 1b, 1f
      if(
        !hex && i < text.size() && (text[i] == 'b' || text[i] == 'f') &&
        (i + 1 == text.size() || !is_identifier_char(text[i + 1], syntax)))
      {
        asm_tokent token{asm_tokent::kindt::LOCAL_LABEL, digits};
        token.backward = text[i] == 'b';
        tokens.push_back(token);
        ++i;
        continue;
      }

      if(i < text.size() && is_identifier_char(text[i], syntax))
      {
        error = "malformed number";
        return false;
      }

      asm_tokent token{asm_tokent::kindt::NUMBER, digits};
      token.number =
        hex ? string2integer(digits.substr(2), 16) : string2integer(digits, 10);
      tokens.push_back(token);
      continue;
    }

    if(is_identifier_start(c, syntax))
    {
      std::size_t start = i;
      while(i < text.size() && is_identifier_char(text[i], syntax))
        ++i;
      tokens.push_back(
        {asm_tokent::kindt::IDENTIFIER, text.substr(start, i - start)});
      continue;
    }

    if(c == '"')
    {
      std::string contents;
      ++i;
      while(i < text.size() && text[i] != '"')
      {
        if(text[i] == '\\' && i + 1 < text.size())
          ++i;
        contents += text[i++];
      }
      ++i;
      tokens.push_back({asm_tokent::kindt::STRING, contents});
      continue;
    }

    tokens.push_back({asm_tokent::kindt::PUNCTUATION, std::string(1, c)});
    ++i;
  }

  return true;
}

bool split_asm_template(
  const std::string &text,
  const asm_syntaxt &syntax,
  const asm_operandst *operands,
  std::vector<asm_instructiont> &instructions,
  std::string &error)
{
  for(const auto &statement : split_statements(text, syntax))
  {
    asm_token_listt tokens;
    if(!tokenize(statement, syntax, operands, tokens, error))
    {
      error += " in '" + statement + "'";
      return false;
    }

    asm_instructiont instruction;
    instruction.text = statement;

    std::size_t pos = 0;

    // labels: `name:` or `1:`
    while(pos + 1 < tokens.size() && tokens[pos + 1].is_punctuation(':') &&
          (tokens[pos].kind == asm_tokent::kindt::IDENTIFIER ||
           tokens[pos].kind == asm_tokent::kindt::NUMBER))
    {
      instruction.labels.push_back(tokens[pos].text);
      pos += 2;
    }

    // prefixes and mnemonic
    while(pos < tokens.size() && tokens[pos].is_identifier())
    {
      const std::string word = to_lower(tokens[pos].text);
      ++pos;
      if(
        std::find(syntax.prefixes.begin(), syntax.prefixes.end(), word) !=
        syntax.prefixes.end())
      {
        instruction.prefixes.push_back(word);
        continue;
      }
      instruction.mnemonic = word;
      break;
    }

    if(instruction.mnemonic.empty() && pos < tokens.size())
    {
      error = "cannot parse '" + statement + "'";
      return false;
    }

    // operands, split at top-level commas
    int depth = 0;
    asm_token_listt current;
    for(; pos < tokens.size(); ++pos)
    {
      const auto &token = tokens[pos];
      if(token.is_punctuation('(') || token.is_punctuation('['))
        ++depth;
      else if(token.is_punctuation(')') || token.is_punctuation(']'))
        --depth;

      if(depth == 0 && token.is_punctuation(','))
      {
        instruction.operands.push_back(current);
        current.clear();
      }
      else
        current.push_back(token);
    }
    if(!current.empty())
      instruction.operands.push_back(current);

    if(
      instruction.labels.empty() && instruction.prefixes.empty() &&
      instruction.mnemonic.empty())
    {
      continue;
    }

    instructions.push_back(instruction);
  }

  return true;
}
