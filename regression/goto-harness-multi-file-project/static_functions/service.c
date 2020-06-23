#include "service.h"
#include <assert.h>

// contents of the struct
// (mostly just a vtable)

struct service
{
  void (*serve)(void);
};

void service_serve(service_t *service)
{
  service->serve();
}

static void default_serve(void)
{
  assert(0 && "default serve should fail so we can see it is being called");
}

// this static initialisation should not show up in output
// in fact, there is a bit of a bug with dump-c where this
// initialisation would appear but the default_serve function
// would be omitted in certain cases.
static service_t default_service = {.serve = default_serve};

service_t *get_default_service(void)
{
  return &default_service;
}
