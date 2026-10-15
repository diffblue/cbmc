#include <assert.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <fcntl.h>
#include <errno.h>

// Test realistic usage scenario with syscall
// This demonstrates how syscall can be used as an alternative to standard library functions

int main()
{
  // Example 1: Use syscall to read from stdin
  char read_buffer[64];
  long bytes_read = syscall(SYS_read, STDIN_FILENO, read_buffer, sizeof(read_buffer));
  
  // Verify read constraints
  assert(bytes_read >= -1);
  assert(bytes_read <= (long)sizeof(read_buffer));
  
  if(bytes_read > 0) {
    // If we read some data, it should be within the buffer
    assert(bytes_read <= (long)sizeof(read_buffer));
  }
  
  // Example 2: Use syscall to write to stdout
  const char message[] = "Hello from syscall\n";
  long bytes_written = syscall(SYS_write, STDOUT_FILENO, message, sizeof(message)-1);
  
  assert(bytes_written >= -1);
  if(bytes_written > 0) {
    assert(bytes_written <= (long)(sizeof(message)-1));
  }
  
  // Example 3: Open a file using syscall
  long fd = syscall(SYS_open, "/tmp/test_file", O_RDWR | O_CREAT, 0644);
  assert(fd >= -1);
  
  if(fd >= 0) {
    // File opened successfully, now write to it
    const char data[] = "test data";
    long write_result = syscall(SYS_write, (int)fd, data, sizeof(data)-1);
    assert(write_result >= -1);
    
    // Close the file
    long close_result = syscall(SYS_close, (int)fd);
    assert(close_result >= -1);
  }
  
  // Example 4: Get process information
  long pid = syscall(SYS_getpid);
  assert(pid > 0); // PIDs are always positive
  
  long uid = syscall(SYS_getuid);
  assert(uid >= 0); // UIDs are non-negative
  
  // Example 5: Create a pipe using syscall
  int pipefd[2];
  long pipe_result = syscall(SYS_pipe, pipefd);
  assert(pipe_result >= -1);
  
  if(pipe_result == 0) {
    // Pipe created successfully
    assert(pipefd[0] >= 0);
    assert(pipefd[1] >= 0);
    assert(pipefd[0] != pipefd[1]); // Read and write ends should be different
    
    // Write to pipe and read from it
    const char pipe_data[] = "pipe test";
    long pipe_write = syscall(SYS_write, pipefd[1], pipe_data, sizeof(pipe_data)-1);
    
    if(pipe_write > 0) {
      char pipe_buffer[64];
      long pipe_read = syscall(SYS_read, pipefd[0], pipe_buffer, sizeof(pipe_buffer));
      assert(pipe_read >= 0); // Should read successfully
    }
    
    // Close pipe ends
    syscall(SYS_close, pipefd[0]);
    syscall(SYS_close, pipefd[1]);
  }
  
  return 0;
}
