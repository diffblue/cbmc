// Debian package iaxmodem, spandsp

#ifdef __GNUC__
extern float fabsf (float __x);
extern float cabsf (float _Complex __z);
extern long double fabsl (long double __x);
extern double cabs (double _Complex __z);
extern double fabs (double __x);
extern long double cabsl (long double _Complex __z);

#  define CONCAT(a, b) a##b
#  define CONCAT2(a, b) CONCAT(a, b)

#  define STATIC_ASSERT(condition)                                             \
    int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]
#endif

int main()
{
  #ifdef __GNUC__
  // expansion of fabs
  double damp;
  (void)(__extension__(__builtin_classify_type (__real__ ((__typeof__ (damp)) 0)) == 8));
  float famp;
  (void)(__extension__(
      __typeof__(__real__(
          __typeof__(*(
              (__typeof__(
                  (__typeof__(
                      (__typeof__ (famp)) 0) *) 0 ))
              0)))
        0)) famp);

  float v1;
  STATIC_ASSERT(
    __builtin_classify_type((__typeof__ (*(0 ?
                                           (__typeof__ (0 ?
                                                        (double *) 0 :
                                                        (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                   (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                    __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 :
                                           (__typeof__ (0 ?
                                                        (__typeof__ ((__typeof__ (famp)) 0) *) 0 :
                                                        (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                     (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                      __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0)))0)
    ==
    __builtin_classify_type((float)0));

  v1 = (__extension__ ((sizeof (__real__ (famp)) == sizeof (double) ||
                        __builtin_classify_type (__real__ (famp)) != 8) ?
                       ((sizeof (__real__ (famp)) == sizeof (famp)) ?
                        (__typeof__ (__real__ (
                              /* type of this subexpression should be float,
                               * according to the STATIC_ASSERT above */
                              __typeof__ (*(0 ?
                                            (__typeof__ (0 ?
                                                         (double *) 0 :
                                                         (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                    (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                     __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 :
                                            (__typeof__ (0 ?
                                                         (__typeof__ ((__typeof__ (famp)) 0) *) 0 :
                                                         (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                      (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                       __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0))) 0)) fabs (famp) :
                        (__typeof__ (__real__ (__typeof__ (*(0 ?
                                                             (__typeof__ (0 ?
                                                                          (double *) 0 :
                                                                          (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                     (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                      __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 : (__typeof__ (0 ?
                                                                                                                                                                            (__typeof__ ((__typeof__ (famp)) 0) *) 0 : (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                    (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                     __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0))) 0)) cabs (famp)) :
                                                                                                                                                                                                                                    (sizeof (__real__ (famp)) == sizeof (float)) ?
                                                                                                                                                                                                                                    ((sizeof (__real__ (famp)) == sizeof (famp)) ?
                                                                                                                                                                                                                                     (__typeof__ (__real__ (__typeof__ (*(0 ?
                                                                                                                                                                                                                                                                          (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                       (double *) 0 :
                                                                                                                                                                                                                                                                                       (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                  (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                   __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 :
                                                                                                                                                                                                                                                                          (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                       (__typeof__ ((__typeof__ (famp)) 0) *) 0 : (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                                               (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                                                __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0))) 0)) fabsf (famp) :
                                                                                                                                                                                                                                     (__typeof__ (__real__ (__typeof__ (*(0 ?
                                                                                                                                                                                                                                                                          (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                       (double *) 0 : (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                 (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                  __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 : (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__typeof__ ((__typeof__ (famp)) 0) *) 0 : (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0))) 0)) cabsf (famp)) :
                                                                                                                                                                                                                                    ((sizeof (__real__ (famp)) == sizeof (famp)) ?
                                                                                                                                                                                                                                     (__typeof__ (__real__ (__typeof__ (*(0 ?
                                                                                                                                                                                                                                                                          (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                       (double *) 0 : (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                 (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                  __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 : (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__typeof__ ((__typeof__ (famp)) 0) *) 0 : (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0))) 0)) fabsl (famp) :
                                                                                                                                                                                                                                     (__typeof__ (__real__ (__typeof__ (*(0 ?
                                                                                                                                                                                                                                                                          (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                       (double *) 0 : (void *) ((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                 (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                  __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8))))) 0 : (__typeof__ (0 ?
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__typeof__ ((__typeof__ (famp)) 0) *) 0 : (void *) (!((__builtin_classify_type ((__typeof__ (famp)) 0) == 8 ||
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__builtin_classify_type ((__typeof__ (famp)) 0) == 9 &&
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         __builtin_classify_type (__real__ ((__typeof__ (famp)) 0)) == 8)))))) 0))) 0)) cabsl (famp))));
  #endif

  return 0;
}
