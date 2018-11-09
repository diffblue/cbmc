/// \file Test that goto_program2code adds locations to compound blocks
///
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_COMPOUND_BLOCK_LOCATIONS_H
#define CPROVER_COMPOUND_BLOCK_LOCATIONS_H

#include <util/irep.h>
#include <util/std_expr.h>

#include <string>

class compound_block_locationst
{
public:
  compound_block_locationst()
    : types({
        {ID_dowhile, "dowhile"},
        {ID_for, "for"},
        {ID_ifthenelse, "ifthenelse"},
        {ID_switch, "switch"},
        {ID_while, "while"},
      })
  {
  }

  /// For each pair of \ref codet type and line number in expected, check that
  /// there's a goto-instruction of that type with that line number in prog
  /// after running goto_program2code on it.
  void check(
    const std::string &prog,
    const std::list<std::pair<const irep_idt, const unsigned>> &expected);

protected:
  void check_compound_block_locations(
    const std::string &prog,
    const std::list<std::pair<const irep_idt, const unsigned>> &expected);

  void recurse_on_block(
    const exprt &,
    std::list<std::pair<const irep_idt, const unsigned>> &);

  const std::unordered_map<const irep_idt, const std::string, irep_id_hash>
    types;
};

#endif // CPROVER_COMPOUND_BLOCK_LOCATIONS_H
