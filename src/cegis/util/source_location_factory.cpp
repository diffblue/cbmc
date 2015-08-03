#include <cegis/options/literals.h>
#include <cegis/util/source_location_factory.h>

source_location_factoryt::source_location_factoryt()
{
}

source_location_factoryt::~source_location_factoryt()
{
}

source_locationt source_location_factoryt::operator ()(
    const std::string &func_name)
{
  source_locationt loc;
  loc.set_file(SYNTHESIS_MODULE);
  loc.set_line(++line_counters[func_name]);
  loc.set_function(func_name);
  return loc;
}
