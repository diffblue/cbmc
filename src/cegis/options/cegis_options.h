/*******************************************************************
 Module:  Counterexample-Guided Inductive Synthesis

 Authors: Daniel Kroening, kroening@kroening.com
 Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CEGIS_CEGIS_OPTIONS_H_
#define CEGIS_CEGIS_OPTIONS_H_

#include <list>
#include <string>

/**
 * @brief
 *
 * @details
 */
class cegis_optionst
{
  const class cmdlinet &cmdline;
  const class optionst &options;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param cmdline
   * @param options
   */
  cegis_optionst(const cmdlinet &cmdline, const optionst &options);

  /**
   * @brief
   *
   * @details
   */
  ~cegis_optionst();

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::string entry_function_name() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::string root_function_name() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  std::list<std::string> target_function_names() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  size_t max_prog_size() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  const optionst &get_options() const;
};

#endif /* CEGIS_CEGIS_OPTIONS_H_ */
