# syscall() Model Implementation

## Overview

This document describes the implementation of the `syscall()` model for CBMC's C library, as requested in issue [#7646](https://github.com/diffblue/cbmc/issues/7646).

## Background

The `syscall()` function provides a generic interface to invoke system calls directly by their system call number. It is defined as:

```c
long syscall(long number, ...);
```

This is a variadic function where the first argument is the system call number (e.g., `SYS_read`, `SYS_write`, `SYS_open`), and the remaining arguments depend on the specific system call being invoked.

## Implementation Approach

The implementation follows the approach discussed in [Kani issue #2284](https://github.com/model-checking/kani/issues/2284), which suggests:

1. **Delegation to existing models**: Where possible, delegate to already-implemented models for specific system calls
2. **Safe overapproximation**: For unmodeled system calls, provide non-deterministic return values with appropriate constraints

### File Location

- **Model implementation**: `src/ansi-c/library/syscall.c`
- **Test cases**: 
  - `regression/cbmc-library/syscall-01/` - Basic syscall functionality
  - `regression/cbmc-library/syscall-02/` - Unmodeled syscall handling

## Modeled System Calls

The following system calls are explicitly handled by delegating to existing models:

### I/O Operations
- **SYS_read**: Delegates to `read()` model (from unistd.c)
- **SYS_write**: Delegates to `write()` model (from unistd.c)
- **SYS_open**: Delegates to `__CPROVER_open()` model (from fcntl.c)
- **SYS_close**: Delegates to `close()` model (from unistd.c)
- **SYS_creat**: Delegates to `__CPROVER_creat()` model (from fcntl.c)
- **SYS_openat**: Delegates to `__CPROVER_openat()` model (from fcntl.c)
- **SYS_fcntl**: Delegates to `__CPROVER_fcntl()` model (from fcntl.c)

### File Descriptor Operations
- **SYS_dup**: Models file descriptor duplication with non-deterministic return
- **SYS_dup2**: Models file descriptor duplication to specific fd
- **SYS_dup3**: Models file descriptor duplication with flags
- **SYS_lseek**: Models file offset repositioning

### Process/Thread Information
- **SYS_getpid**: Returns non-deterministic positive process ID
- **SYS_getuid**: Returns non-deterministic non-negative user ID
- **SYS_getgid**: Returns non-deterministic non-negative group ID
- **SYS_geteuid**: Returns non-deterministic non-negative effective user ID
- **SYS_getegid**: Returns non-deterministic non-negative effective group ID
- **SYS_gettid**: Returns non-deterministic positive thread ID

### Other Operations
- **SYS_pipe**: Delegates to `pipe()` model (from unistd.c)
- **SYS_unlink**: Delegates to `unlink()` model (from unistd.c)

## Unmodeled System Calls

For system calls that don't have explicit models, the implementation provides a safe overapproximation:

1. Returns a non-deterministic `long` value
2. Models potential error conditions by non-deterministically setting the return value to -1
3. When an error is indicated (return value = -1), sets `errno` to a non-deterministic positive value

This approach ensures soundness in verification while allowing the analysis to continue even when encountering unmodeled system calls.

## Design Decisions

### 1. Conditional Compilation

The implementation uses `#ifdef SYS_xxx` guards for each system call number. This is because:
- System call numbers are architecture-dependent
- Not all system calls are available on all platforms (e.g., Windows vs. Linux)
- This ensures the model compiles on different platforms

### 2. Variadic Argument Handling

The implementation uses `va_list` to handle the variable number of arguments:
```c
va_list ap;
va_start(ap, number);
// ... extract arguments with va_arg()
va_end(ap);
```

### 3. Delegation Pattern

Where possible, system calls delegate to existing models:
```c
if(number == SYS_read)
{
  int fd = va_arg(ap, int);
  void *buf = va_arg(ap, void *);
  size_t count = va_arg(ap, size_t);
  result = (long)read(fd, buf, count);
  va_end(ap);
  return result;
}
```

This ensures:
- Consistency with existing models
- Reuse of well-tested verification logic
- Reduced duplication of code

### 4. Error Modeling

Error conditions are modeled consistently:
```c
if(retval == -1)
{
  errno = __VERIFIER_nondet_int();
  __CPROVER_assume(errno > 0); // errno values are positive
}
```

## Testing

Two test cases are provided:

### syscall-01
Tests basic functionality:
- Delegation to existing models works correctly
- Return values are in valid ranges
- Process/thread ID syscalls return appropriate values
- Error conditions properly set errno

### syscall-02
Tests unmodeled syscall handling:
- Unknown syscall numbers return non-deterministic values safely
- Error conditions are modeled correctly
- Additional syscalls (dup, dup2, lseek) work as expected

## Future Extensions

The model can be extended to support additional system calls by:

1. Adding a new `#ifdef SYS_xxx` block in the syscall function
2. Either delegating to an existing model or providing a new model inline
3. Adding test cases to verify the new functionality

Common candidates for future additions:
- Memory mapping operations (mmap, munmap, mprotect)
- Socket operations (socket, bind, listen, accept, connect)
- Signal handling (sigaction, sigprocmask)
- File system operations (stat, fstat, chmod, chown)
- Process control (fork, exec, wait)

## References

- Original issue: https://github.com/diffblue/cbmc/issues/7646
- Implementation guidance: https://github.com/model-checking/kani/issues/2284
- POSIX syscall specification: https://pubs.opengroup.org/onlinepubs/9699919799/functions/V2_chap02.html

## Architecture Notes

### System Call Numbers

System call numbers vary significantly across architectures:

- **x86-64 Linux**: SYS_read=0, SYS_write=1, SYS_open=2, SYS_close=3
- **x86 (32-bit) Linux**: SYS_read=3, SYS_write=4, SYS_open=5, SYS_close=6
- **ARM**: Different numbering scheme
- **Windows**: Does not use POSIX system calls

The model uses the platform-provided definitions from `<sys/syscall.h>` to ensure correctness across platforms.

## Verification Considerations

When using this model in CBMC verification:

1. **Non-determinism**: Unmodeled syscalls introduce non-determinism, which is sound but may increase analysis complexity
2. **Path explosion**: Testing multiple syscalls may lead to path explosion; consider using `--unwind` bounds
3. **Errno handling**: Always check errno after syscall returns -1 to ensure proper error handling
4. **Platform dependencies**: Be aware that syscall availability and behavior is platform-dependent

## Maintenance

When updating the model:

1. Ensure compatibility with existing models in the library
2. Add appropriate test cases
3. Update this documentation
4. Consider adding architecture-specific handling if needed
5. Test on multiple platforms (Linux, macOS, Windows with Cygwin)
