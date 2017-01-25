/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_JSA_GENETIC_JSA_SERIALISER_H
#define CPROVER_CEGIS_JSA_GENETIC_JSA_SERIALISER_H

#include <functional>

/**
 * @brief
 *
 * @details
 */
class jsa_serialisert
{
  const class jsa_programt &prog;
public:
  /**
   * @brief
   *
   * @details
   *
   * @param prog
   */
  explicit jsa_serialisert(const jsa_programt &prog);

  /**
   * @brief
   *
   * @details
   *
   * @param sdu
   * @param entity
   */
  void operator()(class irept &sdu, const class jsa_genetic_solutiont &entity) const;

  /**
   * @brief
   *
   * @details
   *
   * @param entity
   * @param sdu
   */
  void operator()(class jsa_genetic_solutiont &entity, const irept &sdu) const;

  /**
   * @brief
   *
   * @details
   *
   * @param entity
   * @param sdu
   */
  void operator()(class jsa_solutiont &entity, const irept &sdu) const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  operator std::function<void(irept &, const jsa_genetic_solutiont &)>() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  operator std::function<void(jsa_genetic_solutiont &, const irept &)>() const;

  /**
   * @brief
   *
   * @details
   *
   * @return
   */
  operator std::function<void(jsa_solutiont &, const irept &)>() const;
};

#endif // CPROVER_CEGIS_JSA_GENETIC_JSA_SERIALISER_H
