#include <assert.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <fcntl.h>
#include <errno.h>

// Test basic syscall functionality
// This test verifies that the syscall model properly delegates to 
// existing models and handles errors correctly

int main()
{
  char buf[100];
  int pipefd[2];
  
  // Test SYS_getpid - should return positive value
  long pid = syscall(SYS_getpid);
  assert(pid > 0);
  
  // Test SYS_getuid - should return non-negative value
  long uid = syscall(SYS_getuid);
  assert(uid >= 0);
  
  // Test SYS_getgid - should return non-negative value  
  long gid = syscall(SYS_getgid);
  assert(gid >= 0);
  
  // Test SYS_read - delegates to read model
  // Result should be in valid range
  long bytes_read = syscall(SYS_read, 0, buf, sizeof(buf));
  assert(bytes_read >= -1 && bytes_read <= (long)sizeof(buf));
  
  // Test SYS_write - delegates to write model
  long bytes_written = syscall(SYS_write, 1, buf, sizeof(buf));
  assert(bytes_written >= -1 && bytes_written <= (long)sizeof(buf));
  
  // Test SYS_open - delegates to open model
  long fd = syscall(SYS_open, "test_file", O_RDONLY);
  assert(fd >= -1);
  
  // Test SYS_close - delegates to close model
  if(fd >= 0) {
    long close_result = syscall(SYS_close, (int)fd);
    assert(close_result >= -1);
  }
  
  // Test SYS_pipe - delegates to pipe model
  long pipe_result = syscall(SYS_pipe, pipefd);
  assert(pipe_result >= -1);
  if(pipe_result == 0) {
    // Pipe succeeded, file descriptors should be valid
    assert(pipefd[0] >= 0);
    assert(pipefd[1] >= 0);
  }
  
  // Test error conditions - if return is -1, errno should be set
  long result = syscall(SYS_open, "nonexistent", O_RDONLY);
  if(result == -1) {
    // errno should be positive when error occurred
    assert(errno > 0);
  }
  
  return 0;
}
