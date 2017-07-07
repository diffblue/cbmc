extern void* memset(void *, int, unsigned long);

typedef void (*__sighandler_t) (int);

typedef __sighandler_t sighandler_t;

typedef struct siginfo {
  int si_signo;
} siginfo_t;

struct sigaction {
  union {
    __sighandler_t _sa_handler;
    void (*_sa_sigaction)(int, struct siginfo *, void *);
  } _u;
};

#define sa_sigaction  _u._sa_sigaction
#define sa_handler  _u._sa_handler

static void askpass_timeout(signed int ignore) {
  ;
}

int main() {
  struct sigaction sa, oldsa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = askpass_timeout;
  return 0;
}
