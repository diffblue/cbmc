#include <stddef.h>

// common pattern:
// Some sort of interface defined over "abstract" type with hidden
// implementation details, effectively C style OOP
//
// This is a straw example of course, but very reminiscent of patterns that
// occur in real programs

typedef struct service service_t;

service_t *get_default_service(void);
void service_serve(service_t *service);
