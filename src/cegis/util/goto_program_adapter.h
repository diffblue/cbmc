#ifndef CEGIS_GOTO_PROGRAM_ADAPTER_H_
#define CEGIS_GOTO_PROGRAM_ADAPTER_H_

#include <string>
#include <util/source_location.h>

/**
 * @brief
 *
 * @details
 */
class goto_program_adaptert
{
  class symbol_tablet &symbol_table;
  class goto_programt &goto_program;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param symbol_table
   * @param goto_program
   */
  goto_program_adaptert(symbol_tablet &symbol_table,
      goto_programt &goto_program);

  /**
   * @brief
   *
   * @details
   */
  ~goto_program_adaptert();

  /**
   * @brief
   *
   * @details
   *
   * @param identifier
   * @param type
   *
   * @return
   */
  class code_declt &append_decl(const irep_idt &identifier,
      const class typet &type) const;

  /**
   * @brief
   *
   * @details
   *
   * @param identifier
   * @param type
   * @param location
   *
   * @return
   */
  class code_declt &append_decl(const irep_idt &identifier, const typet &type,
      const class source_locationt &location) const;

  /**
   * @brief
   *
   * @details
   *
   * @param identifier
   * @param type
   * @param value
   * @param location
   *
   * @return
   */
  class code_declt &append_decl(const irep_idt &identifier, const typet &type,
      const class exprt &value, const source_locationt &location) const;
};

/**
 * @brief
 *
 * @details
 *
 * @param gf
 * @param name
 *
 * @return
 */
goto_programt &get_program_body(class goto_functionst &gf,
    const std::string &name);

/**
 * @see
 */
const goto_programt &get_program_body(const goto_functionst &gf,
    const std::string &name);

#endif /* CEGIS_GOTO_PROGRAM_ADAPTER_H_ */
