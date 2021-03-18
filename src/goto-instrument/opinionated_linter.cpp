#include "opinionated_linter.h"
#include "goto_program2code.h"

#include <util/prefix.h>

#include <iostream>

int goto_hatert::score()
{
  int score = this->max_score();

  // You only get two chances to ruin your program
  const int decrement = this->max_score() / 2;

  std::list<irep_idt> emp_l;
  std::unordered_set<irep_idt> emp_s;
  std::set<std::string> emp_ss;
  for(auto &gf : this->gm.goto_functions.function_map)
  {
    if(has_prefix(id2string(gf.first), CPROVER_PREFIX))
      continue;
    if(!gf.second.body.instructions.size())
      continue;
    code_blockt dst;
    goto_program2codet g2c(
      gf.first, gf.second.body, gm.symbol_table, dst, emp_l, emp_l, emp_s,
      emp_ss);
    g2c();
    for(const auto &code : dst.statements())
      if(code.get_statement() == ID_label)
        score -= decrement;
  }
  return score;
}

int goto_hatert::max_score()
{
  int n_insts = 0;
  for(const auto &gf : this->gm.goto_functions.function_map)
  {
    if(has_prefix(id2string(gf.first), CPROVER_PREFIX))
      continue;
    if(!gf.second.body.instructions.size())
      continue;
    n_insts += gf.second.body.instructions.size();
  }
  return n_insts;
}

int average_fun_lengtht::score()
{
  int n_insts = 0;
  for(const auto &gf : this->gf.function_map)
    n_insts += gf.second.body.instructions.size();

  int avg_length = n_insts / this->max_score();
  int final_score = 0;


  for(const auto len : this->boundaries)
  {
    if(avg_length > len)
      return final_score;
    final_score += 1;
  }
  return final_score;
}

int average_fun_lengtht::max_score()
{
  return this->boundaries.size();
}

void considered_harmfult::operator()()
{
  int possible_score = 0;
  int actual_score = 0;
  for(const auto analysis : this->analyses)
  {
    possible_score += analysis->max_score();
    actual_score += analysis->score();
  }

  int normalized = actual_score * 100 / possible_score;

  for(const auto &pair : this->score_map)
  {
    if(normalized < pair.first)
    {
      this->log.status() << pair.second << log.eom;
      return;
    }
  }
}
