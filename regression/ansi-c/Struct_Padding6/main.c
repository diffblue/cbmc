#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#pragma pack(4)

typedef unsigned short domid_t;
typedef unsigned evtchn_port_t;
struct evtchn_status {
    domid_t dom;
    evtchn_port_t port;
    unsigned status;
    unsigned vcpu;
    union {
        struct {
            domid_t dom;
        } unbound;
        struct {
            domid_t dom;
            evtchn_port_t port;
        } interdomain;
        unsigned pirq;
        unsigned virq;
    } u;
    char a;
};

int main()
{
  #ifdef __GNUC__
  STATIC_ASSERT(__builtin_offsetof(struct evtchn_status,u.interdomain.port)==20);
  #endif

  STATIC_ASSERT(sizeof(struct evtchn_status)==28);
  return 0;
};
