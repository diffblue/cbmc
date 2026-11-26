#include <assert.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <errno.h>

// Test syscall handling of unmodeled system calls
// This verifies that unmodeled syscalls return safe non-deterministic values

int main()
{
  // Use a very high syscall number that is unlikely to be modeled
  // This tests the default case in the syscall model
  long unknown_syscall_result = syscall(9999);
  
  // The result could be anything, but if it's -1, errno should be positive
  if(unknown_syscall_result == -1) {
    assert(errno > 0);
  }
  
  // Test that we can handle multiple unknown syscalls
  long result1 = syscall(9998);
  long result2 = syscall(9997);
  
  // These may or may not be equal - non-deterministic
  // But they should be valid return values
  
  // Test dup family syscalls which have simple models
#ifdef SYS_dup
  int fd = 5; // arbitrary file descriptor
  long dup_result = syscall(SYS_dup, fd);
  assert(dup_result >= -1);
  if(dup_result == -1) {
    // errno should be set on error
    assert(errno > 0);
  }
#endif

#ifdef SYS_dup2
  int oldfd = 5;
  int newfd = 10;
  long dup2_result = syscall(SYS_dup2, oldfd, newfd);
  assert(dup2_result >= -1);
  if(dup2_result == -1) {
    assert(errno > 0);
  }
#endif

#ifdef SYS_lseek
  int seek_fd = 5;
  off_t offset = 100;
  int whence = 0; // SEEK_SET
  long lseek_result = syscall(SYS_lseek, seek_fd, offset, whence);
  // lseek can return any value including -1 for error
  if(lseek_result == -1) {
    assert(errno > 0);
  }
#endif

  return 0;
}
