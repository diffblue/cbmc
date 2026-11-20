/*******************************************************************\

Module: Unit tests for split_asm_template

Author: Michael Tautschnig

\*******************************************************************/

#include <assembler/asm_operands.h>
#include <assembler/asm_template.h>
#include <testing-utils/use_catch.h>

static asm_syntaxt x86_like_syntax()
{
  asm_syntaxt syntax;
  syntax.line_comments = {"#"};
  syntax.prefixes = {"lock", "rep"};
  return syntax;
}

TEST_CASE("split_asm_template", "[core][assembler][asm_template]")
{
  const asm_syntaxt syntax = x86_like_syntax();
  std::vector<asm_instructiont> instructions;
  std::string error;

  SECTION("labels, prefixes, comments, and separators")
  {
    REQUIRE(split_asm_template(
      "1: lock; xaddl $1, (%rax) # comment\n\tjnz 1b",
      syntax,
      nullptr,
      instructions,
      error));
    REQUIRE(instructions.size() == 3);

    // the label and the prefix form a statement of their own
    REQUIRE(instructions[0].labels == std::vector<std::string>{"1"});
    REQUIRE(instructions[0].prefixes == std::vector<std::string>{"lock"});
    REQUIRE(instructions[0].mnemonic.empty());

    REQUIRE(instructions[1].mnemonic == "xaddl");
    REQUIRE(instructions[1].operands.size() == 2);
    REQUIRE(instructions[1].operands[0][0].is_punctuation('$'));

    REQUIRE(instructions[2].mnemonic == "jnz");
    REQUIRE(instructions[2].operands.size() == 1);
    const asm_tokent &target = instructions[2].operands[0][0];
    REQUIRE(target.kind == asm_tokent::kindt::LOCAL_LABEL);
    REQUIRE(target.backward);
  }

  SECTION("operand references")
  {
    asm_operandst operands;
    operands.operands.resize(2);
    operands.operands[1].name = "value";

    REQUIRE(split_asm_template(
      "movl %k[value], %0", syntax, &operands, instructions, error));
    REQUIRE(instructions.size() == 1);
    REQUIRE(instructions[0].operands.size() == 2);

    const asm_tokent &named = instructions[0].operands[0][0];
    REQUIRE(named.kind == asm_tokent::kindt::OPERAND);
    REQUIRE(named.index == 1);
    REQUIRE(named.modifier == "k");

    const asm_tokent &numbered = instructions[0].operands[1][0];
    REQUIRE(numbered.kind == asm_tokent::kindt::OPERAND);
    REQUIRE(numbered.index == 0);
    REQUIRE(numbered.modifier.empty());
  }

  SECTION("references to operands that do not exist")
  {
    asm_operandst operands;
    operands.operands.resize(1);
    REQUIRE_FALSE(split_asm_template(
      "movl %1, %0", syntax, &operands, instructions, error));
    REQUIRE_FALSE(error.empty());
  }

  SECTION("basic assembly: % is not special")
  {
    REQUIRE(
      split_asm_template("incl %eax", syntax, nullptr, instructions, error));
    REQUIRE(instructions.size() == 1);
    REQUIRE(instructions[0].operands.size() == 1);
    REQUIRE(instructions[0].operands[0][0].is_punctuation('%'));
  }
}
