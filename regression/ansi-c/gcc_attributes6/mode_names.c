#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__

// GCC accepts a mode name with or without a surrounding pair of
// underscores: mode(byte) is the same as mode(__byte__).  Linux uses
// __mode(byte) on enums in net/rxrpc/ar-internal.h and include/trace/events.
enum F
{
  X,
  Y
} __attribute__((__mode__(byte)));
STATIC_ASSERT(sizeof(enum F) == 1);
#  ifndef __cplusplus
// The C++ front end fails these with an invariant violation in
// static_lifetime_init (also with mode(__byte__), and on develop).
STATIC_ASSERT((enum F)(-1) > 0);
#  endif

enum Fs
{
  Xs = -1
} __attribute__((mode(QI)));
STATIC_ASSERT(sizeof(enum Fs) == 1);
#  ifndef __cplusplus
STATIC_ASSERT((enum Fs)(-1) < 0);
#  endif

typedef int qi_t __attribute__((mode(QI)));
STATIC_ASSERT(sizeof(qi_t) == 1);
typedef unsigned uhi_t __attribute__((mode(HI)));
STATIC_ASSERT(sizeof(uhi_t) == 2);
typedef float df_t __attribute__((mode(DF)));
STATIC_ASSERT(sizeof(df_t) == 8);
typedef _Complex float dc_t __attribute__((mode(DC)));
STATIC_ASSERT(sizeof(dc_t) == 16);

// The modes below are not accepted by GCC; they test CBMC's fallback for mode
// names it does not recognise.
// GCC rejects OI ("unable to emulate 'OI'"); CBMC falls back to the enum's
// natural underlying type.  This only checks that the fallback no longer
// makes the enum its own underlying type, which crashed layout computation.
enum G
{
  P,
  Q
} __attribute__((mode(OI)));
STATIC_ASSERT(sizeof(enum G) == sizeof(int));

// A single pair of underscores is only stripped when it surrounds the name:
// GCC rejects __QI as an unknown mode, and CBMC must not treat it as QI.
enum H
{
  R
} __attribute__((mode(__QI)));
STATIC_ASSERT(sizeof(enum H) == sizeof(int));

struct s
{
  char c;
  enum F f;
  enum G g;
};
#  ifndef __cplusplus
// The C++ front end cannot evaluate sizeof of a struct in this array size
// (also without mode attributes, and on develop).
STATIC_ASSERT(sizeof(struct s) == 2 * sizeof(int));
#  endif

#endif

int main()
{
}
