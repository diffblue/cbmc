#ifndef CEGIS_SOURCE_LOCATION_FACTORY_H_
#define CEGIS_SOURCE_LOCATION_FACTORY_H_

#include <util/source_location.h>

/**
 * @brief
 *
 * @details
 */
class source_location_factoryt
{
  std::map<std::string, unsigned int> line_counters;
public:
  /**
   * @brief
   *
   * @details
   */
  source_location_factoryt();

  /**
   * @brief
   *
   * @details
   */
  ~source_location_factoryt();

  /**
   * @brief
   *
   * @details
   *
   * @param func_name
   *
   * @return
   */
  source_locationt operator()(const std::string &func_name);
};

#endif /* CEGIS_SOURCE_LOCATION_FACTORY_H_ */
