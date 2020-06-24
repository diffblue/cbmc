#include "service.h"

// this isn't testing any interesting harness
// properties so we just have a main function
// with no parameters
int main(void)
{
  service_t *service = get_default_service();
  service_serve(service);
}
