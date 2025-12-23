#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <time.h>

// MSVC doesn't have CLOCK_* macros
#ifdef _WIN32
#  define CLOCK_MONOTONIC 1
#  define CLOCK_REALTIME 1
int clock_gettime(int clockid, struct timespec *tp);
#endif

// Test function from the issue description
uint32_t my_time(void)
{
  struct timespec t;
  int ret = clock_gettime(CLOCK_MONOTONIC, &t);

  // If clock_gettime fails, return a safe value
  if(ret != 0)
  {
    return 0;
  }

  return (t.tv_nsec / 1000000) + ((t.tv_sec % 86400) * 1000);
}

int main()
{
  // Test null pointer behavior
  int result_null = clock_gettime(CLOCK_REALTIME, 0);
  if(result_null == -1)
  {
    // errno should be set to EFAULT for null pointer
    assert(errno == EFAULT);
  }

  struct timespec ts;

  // Test basic functionality with different clock types
  int result1 = clock_gettime(CLOCK_REALTIME, &ts);
  assert(result1 == 0 || result1 == -1);

  if(result1 == 0)
  {
    // If successful, tv_nsec should be in valid range
    assert(ts.tv_nsec >= 0 && ts.tv_nsec <= 999999999L);
  }

  // Test with CLOCK_MONOTONIC
  int result2 = clock_gettime(CLOCK_MONOTONIC, &ts);
  assert(result2 == 0 || result2 == -1);

  if(result2 == 0)
  {
    // If successful, tv_nsec should be in valid range
    assert(ts.tv_nsec >= 0 && ts.tv_nsec <= 999999999L);
  }

  // Test the my_time function from the issue
  // Note: my_time() handles the failure case internally
  uint32_t time_result = my_time();
  // Should return either 0 (on failure) or valid millisecond value within a day
  assert(time_result < 86400000 || time_result == 0);

  return 0;
}
