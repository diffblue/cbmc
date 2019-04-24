#ifdef __GNUC__

#include <inttypes.h>

#  define CONCAT(a, b) a##b
#  define CONCAT2(a, b) CONCAT(a, b)

#  define STATIC_ASSERT(condition)                                             \
    int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// Debian package openvswitch
enum __attribute__((__packed__)) ofpact_type {
  e_1
};

enum __attribute__((__packed__)) ofputil_action_code {
  e_2
};

struct ofpact {
    enum ofpact_type type;      /* OFPACT_*. */
    enum ofputil_action_code compat; /* Original type when added, if any. */
    uint16_t len;               /* Length of the action, in bytes, including
                                 * struct ofpact, excluding padding. */
};

STATIC_ASSERT(sizeof(struct ofpact) == 4);
#endif

int main()
{
}
