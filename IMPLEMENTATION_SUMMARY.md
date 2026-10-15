# syscall() Model Implementation Summary

## Overview

This document summarizes the implementation of the `syscall()` model for CBMC's C library, addressing issue [#7646](https://github.com/diffblue/cbmc/issues/7646).

## Implementation Details

### Files Created/Modified

1. **Model Implementation**
   - **File**: `src/ansi-c/library/syscall.c`
   - **Description**: Complete implementation of the `syscall()` function model
   - **Lines of Code**: ~350 lines

2. **Test Suite**
   - **Test 1**: `regression/cbmc-library/syscall-01/`
     - Tests delegation to existing models
     - Verifies correct return value ranges
     - Tests process/thread ID syscalls
   
   - **Test 2**: `regression/cbmc-library/syscall-02/`
     - Tests unmodeled syscall handling
     - Verifies safe overapproximation
     - Tests additional syscalls (dup, dup2, lseek)
   
   - **Test 3**: `regression/cbmc-library/syscall-03/`
     - Realistic usage scenarios
     - Complex multi-syscall workflows
     - Pipe operations and file I/O

3. **Documentation**
   - **File**: `SYSCALL_MODEL_README.md`
   - **Description**: Comprehensive documentation of the implementation
   - **Contents**: 
     - Implementation approach
     - List of modeled syscalls
     - Design decisions
     - Future extensions
     - Usage examples

## Key Features

### 1. Delegation to Existing Models

The implementation leverages existing models where available:

| System Call | Delegates To | Source File |
|-------------|-------------|-------------|
| SYS_read | `read()` | unistd.c |
| SYS_write | `write()` | unistd.c |
| SYS_open | `__CPROVER_open()` | fcntl.c |
| SYS_close | `close()` | unistd.c |
| SYS_creat | `__CPROVER_creat()` | fcntl.c |
| SYS_openat | `__CPROVER_openat()` | fcntl.c |
| SYS_fcntl | `__CPROVER_fcntl()` | fcntl.c |
| SYS_pipe | `pipe()` | unistd.c |
| SYS_unlink | `unlink()` | unistd.c |

### 2. New Inline Models

The implementation provides inline models for syscalls without existing implementations:

- **File Descriptor Operations**: `dup`, `dup2`, `dup3`, `lseek`
- **Process Information**: `getpid`, `getuid`, `getgid`, `geteuid`, `getegid`, `gettid`

### 3. Safe Overapproximation

For unmodeled syscalls, the implementation:
- Returns non-deterministic `long` values
- Models error conditions (return value = -1, errno > 0)
- Maintains soundness for verification purposes

### 4. Platform Independence

The implementation uses conditional compilation (`#ifdef SYS_xxx`) to:
- Support different architectures (x86, x86-64, ARM, etc.)
- Work across platforms (Linux, macOS, Windows/Cygwin)
- Handle platform-specific syscall availability

## Design Approach

The implementation follows the approach suggested in [Kani issue #2284](https://github.com/model-checking/kani/issues/2284):

1. **Reuse existing work**: Delegate to already-implemented syscall models
2. **Provide safe defaults**: Use non-deterministic values for unmodeled syscalls
3. **Maintain soundness**: Ensure all return values and side effects are correctly modeled

### Code Structure

```c
long syscall(long number, ...)
{
  __CPROVER_HIDE:;
  va_list ap;
  va_start(ap, number);
  
  // Check for each known syscall and delegate
  #ifdef SYS_read
  if(number == SYS_read) {
    // Extract arguments and delegate to read()
    ...
  }
  #endif
  
  // Default case: safe overapproximation
  result = __VERIFIER_nondet_long();
  ...
  va_end(ap);
  return result;
}
```

## Verification Properties

The model ensures the following properties:

1. **Return Value Constraints**
   - Read/write syscalls: `-1 <= result <= requested_size`
   - Open/close syscalls: `result >= -1`
   - Process IDs: `result > 0`
   - User/Group IDs: `result >= 0`

2. **Error Handling**
   - When `result == -1`, errno is set to a positive value
   - Errno values are non-deterministic but constrained

3. **Memory Safety**
   - Buffer accesses are properly bounded
   - Pointer dereferences are checked

## Testing Strategy

### Test Coverage

1. **syscall-01**: Basic functionality
   - Tests 9 different syscalls
   - Verifies delegation works correctly
   - Checks return value constraints

2. **syscall-02**: Edge cases
   - Tests unknown syscall numbers
   - Verifies error handling
   - Tests additional inline models

3. **syscall-03**: Realistic scenarios
   - Multi-step workflows
   - Pipe operations
   - File I/O sequences

### Running Tests

```bash
cd regression/cbmc-library/syscall-01
cbmc main.c --pointer-check --bounds-check

cd ../syscall-02
cbmc main.c --pointer-check --bounds-check

cd ../syscall-03
cbmc main.c --pointer-check --bounds-check
```

Expected output: `VERIFICATION SUCCESSFUL`

## Compatibility

### Tested Platforms

The implementation is designed to work on:
- Linux (x86, x86-64, ARM)
- macOS
- Windows (with Cygwin/MinGW)

### Known Limitations

1. **Architecture-specific syscalls**: Some syscalls may not be available on all platforms
2. **Variadic arguments**: Optional arguments (e.g., mode in open) are handled conservatively
3. **Complex syscalls**: Some syscalls (e.g., ioctl, prctl) are not fully modeled

## Future Work

### Potential Extensions

1. **Memory Management**
   - `mmap`, `munmap`, `mprotect`, `brk`

2. **Socket Operations**
   - `socket`, `bind`, `listen`, `accept`, `connect`, `send`, `recv`

3. **Signal Handling**
   - `sigaction`, `sigprocmask`, `kill`

4. **File System Operations**
   - `stat`, `fstat`, `lstat`, `chmod`, `chown`, `mkdir`, `rmdir`

5. **Process Control**
   - `fork`, `exec*`, `wait`, `waitpid`, `exit`

6. **Advanced I/O**
   - `select`, `poll`, `epoll_*`, `sendfile`

### Enhancement Opportunities

1. **More precise models**: Some inline models could be made more precise
2. **Better errno handling**: Map specific syscalls to specific errno values
3. **Architecture-specific optimizations**: Handle different syscall ABIs
4. **Documentation**: Add more usage examples

## References

- **Original Issue**: https://github.com/diffblue/cbmc/issues/7646
- **Implementation Guidance**: https://github.com/model-checking/kani/issues/2284
- **POSIX Specification**: https://pubs.opengroup.org/onlinepubs/9699919799/
- **Linux Syscall Table**: https://filippo.io/linux-syscall-table/

## Maintenance Notes

### Adding New Syscalls

To add support for a new syscall:

1. Add a new `#ifdef SYS_xxx` block in `syscall.c`
2. Either delegate to an existing model or implement inline
3. Add test cases in a new `syscall-XX/` directory
4. Update documentation

Example:
```c
#ifdef SYS_newsyscall
  if(number == SYS_newsyscall) {
    // Extract arguments
    int arg1 = va_arg(ap, int);
    // Implement or delegate
    result = existing_model(arg1);
    va_end(ap);
    return result;
  }
#endif
```

### Testing Changes

Always run the test suite after modifications:
```bash
cd regression/cbmc-library
make test  # or use the test harness
```

### Code Review Checklist

- [ ] All arguments properly extracted with `va_arg`
- [ ] `va_end()` called on all code paths
- [ ] Return values properly constrained
- [ ] Error conditions (errno) properly modeled
- [ ] Platform guards (`#ifdef`) used appropriately
- [ ] Test cases added/updated
- [ ] Documentation updated

## Acknowledgments

This implementation was guided by:
- The CBMC team's existing library models
- The approach used in Kani's syscall support
- Community feedback on issue #7646

## License

This implementation follows the same license as CBMC (BSD 4-clause).
