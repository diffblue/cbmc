#include <pthread.h>
#include <assert.h>

// ========= Chord library =========

// This struct is not thread-safe itself!
//
// A chord is like a chain of threads `f, g, ...` where `f`
// must terminate before `g` can start to run, and so forth.
struct chord_t
{
  // last thread in chain
  pthread_t thread;
};

// Public function pointer
typedef void *(*start_routine)(void *);

// Internal
struct chord_args_t
{
  // last thread in chain
  pthread_t thread;

  // function pointer for new thread
  start_routine f;

  // argument to f
  void *f_arg;
};

// Internal start routine for a thread in a chord
static void* chord_start_routine(void *ptr)
{
  struct chord_args_t *args = (struct chord_args_t *) ptr; 

  // ignore errors
  pthread_join(args->thread, NULL);
  return args->f(args->f_arg);
}

// This function is not thread-safe itself!
//
// Create a new thread for `f` where `f(arg)` starts to run as
// soon as the currently running `self->thread` has terminated.
//
// \post: self->thread is the newly created thread for `f`
int chord_run(struct chord_t *self, start_routine f, void *arg)
{
  struct chord_args_t args;
  args.thread = self->thread;
  args.f = f;
  args.f_arg = arg;

  return pthread_create(&(self->thread), NULL, chord_start_routine, (void *) &args);
}

// ========= Symbolic test =========

char test_global;

void* test_write_a( void *arg)
{
  test_global = 'A';
  return NULL;
}

void* test_write_b(void *arg)
{
  test_global = 'B';
  return NULL;
}

int main(void)
{
#ifdef _ENABLE_CHORD_
  struct chord_t chord;
  chord_run(&chord, test_write_a, NULL);
  chord_run(&chord, test_write_b, NULL);
#else
  pthread_t a_thread, b_thread;
  pthread_create(&a_thread, NULL, test_write_a, NULL);
  pthread_create(&b_thread, NULL, test_write_b, NULL);
#endif

  char x = test_global;
  char y = test_global;

  // Verification condition:
  //
  //  If global variable equals 'B', then it cannot change.
  //
  // It is expected that this implication
  // fails if _ENABLE_CHORD_ is undefined.
  assert(x != 'B' || y == 'B');

  return 0;
}
