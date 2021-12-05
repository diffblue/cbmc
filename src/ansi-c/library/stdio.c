
/* FUNCTION: putchar */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

/* undefine macros in OpenBSD's stdio.h that are problematic to the checker. */
#if defined(__OpenBSD__)
#undef getchar
#undef putchar
#undef getc
#undef feof
#undef ferror
#undef fileno
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline int putchar(int c)
{
  __CPROVER_HIDE:;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  __CPROVER_printf("%c", c);
  return (error?-1:c);
}

/* FUNCTION: puts */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
int __VERIFIER_nondet_int();

inline int puts(const char *s)
{
  __CPROVER_HIDE:;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  int ret=__VERIFIER_nondet_int();
  __CPROVER_printf("%s\n", s);
  if(error) ret=-1; else __CPROVER_assume(ret>=0);
  return ret;
}

/* FUNCTION: fclose_cleanup */

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
inline void fclose_cleanup(void *stream)
{
__CPROVER_HIDE:;
  __CPROVER_assert(
    !__CPROVER_get_must(stream, "open") || __CPROVER_get_must(stream, "closed"),
    "resource leak: fopen file not closed");
}
#endif

/* FUNCTION: fopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

void fclose_cleanup(void *stream);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

inline FILE *fopen(const char *filename, const char *mode)
{
  __CPROVER_HIDE:;
  (void)*filename;
  (void)*mode;
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(filename), "fopen zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(mode), "fopen zero-termination of 2nd argument");
#endif

  FILE *fopen_result;

  __CPROVER_bool fopen_error=__VERIFIER_nondet___CPROVER_bool();

#if !defined(__linux__) || defined(__GLIBC__)
  fopen_result=fopen_error?NULL:malloc(sizeof(FILE));
#else
  // libraries need to expose the definition of FILE; this is the
  // case for musl
  fopen_result=fopen_error?NULL:malloc(sizeof(int));
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(fopen_result, "open");
  __CPROVER_cleanup(fopen_result, fclose_cleanup);
#endif

  return fopen_result;
}

/* FUNCTION: _fopen */

// This is for Apple; we cannot fall back to fopen as we need
// header files to have a definition of FILE available; the same
// header files rename fopen to _fopen and would thus yield
// unbounded recursion.

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#  include <stdlib.h>
#  define __CPROVER_STDLIB_H_INCLUDED
#endif

void fclose_cleanup(void *stream);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

#ifdef __APPLE__
inline FILE *_fopen(const char *filename, const char *mode)
{
__CPROVER_HIDE:;
  (void)*filename;
  (void)*mode;
#  ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(
    __CPROVER_is_zero_string(filename),
    "fopen zero-termination of 1st argument");
  __CPROVER_assert(
    __CPROVER_is_zero_string(mode), "fopen zero-termination of 2nd argument");
#  endif

  FILE *fopen_result;

  __CPROVER_bool fopen_error = __VERIFIER_nondet___CPROVER_bool();

  fopen_result = fopen_error ? NULL : malloc(sizeof(FILE));

#  ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(fopen_result, "open");
  __CPROVER_cleanup(fopen_result, fclose_cleanup);
#  endif

  return fopen_result;
}
#endif

/* FUNCTION: freopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline FILE* freopen(const char *filename, const char *mode, FILE *f)
{
  __CPROVER_HIDE:;
  (void)*filename;
  (void)*mode;
#if !defined(__linux__) || defined(__GLIBC__)
  (void)*f;
#else
  (void)*(char*)f;
#endif

  return f;
}

/* FUNCTION: fclose */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fclose(FILE *stream)
{
__CPROVER_HIDE:;
#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fclose file must be open");
  __CPROVER_clear_must(stream, "open");
  __CPROVER_set_must(stream, "closed");
#endif
  int return_value=__VERIFIER_nondet_int();
  free(stream);
  return return_value;
}

/* FUNCTION: fdopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

inline FILE *fdopen(int handle, const char *mode)
{
  __CPROVER_HIDE:;
  (void)handle;
  (void)*mode;
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(mode),
    "fdopen zero-termination of 2nd argument");
#endif

#if !defined(__linux__) || defined(__GLIBC__)
  FILE *f=malloc(sizeof(FILE));
#else
  // libraries need to expose the definition of FILE; this is the
  // case for musl
  FILE *f=malloc(sizeof(int));
#endif

  return f;
}

/* FUNCTION: _fdopen */

// This is for Apple; we cannot fall back to fdopen as we need
// header files to have a definition of FILE available; the same
// header files rename fdopen to _fdopen and would thus yield
// unbounded recursion.

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

#ifdef __APPLE__
inline FILE *_fdopen(int handle, const char *mode)
{
  __CPROVER_HIDE:;
  (void)handle;
  (void)*mode;
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(mode),
    "fdopen zero-termination of 2nd argument");
#endif

  FILE *f=malloc(sizeof(FILE));

  return f;
}
#endif

/* FUNCTION: fgets */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
int __VERIFIER_nondet_int();

char *fgets(char *str, int size, FILE *stream)
{
  __CPROVER_HIDE:;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();

  (void)size;
  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fgets file must be open");
#endif

#ifdef __CPROVER_STRING_ABSTRACTION
  int resulting_size;
  __CPROVER_assert(__CPROVER_buffer_size(str)>=size, "buffer-overflow in fgets");
  if(size>0)
  {
    __CPROVER_assume(resulting_size<size);
    __CPROVER_is_zero_string(str)=!error;
    __CPROVER_zero_string_length(str)=resulting_size;
  }
#else
  if(size>0)
  {
    int str_length=__VERIFIER_nondet_int();
    __CPROVER_assume(str_length >= 0 && str_length < size);
    __CPROVER_precondition(__CPROVER_w_ok(str, size), "fgets buffer writable");
    char contents_nondet[str_length];
    __CPROVER_array_replace(str, contents_nondet);
    if(!error)
      str[str_length]='\0';
  }
#endif

  return error?0:str;
}

/* FUNCTION: fread */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

char __VERIFIER_nondet_char();
size_t __VERIFIER_nondet_size_t();

inline size_t fread(
  void *ptr,
  size_t size,
  size_t nitems,
  FILE *stream)
{
  __CPROVER_HIDE:;
  size_t nread=__VERIFIER_nondet_size_t();
  size_t bytes=nread*size;
  __CPROVER_assume(nread<=nitems);

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fread file must be open");
#endif

  for(size_t i=0; i<bytes; i++)
  {
    ((char *)ptr)[i] = __VERIFIER_nondet_char();
  }

  return nread;
}

/* FUNCTION: feof */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int feof(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "feof file must be open");
#endif

  return return_value;
}

/* FUNCTION: ferror */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int ferror(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "feof file must be open");
#endif

  return return_value;
}

/* FUNCTION: fileno */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fileno(FILE *stream)
{
__CPROVER_HIDE:;
  if(stream == stdin)
    return 0;
  else if(stream == stdout)
    return 1;
  else if(stream == stderr)
    return 2;

  int return_value=__VERIFIER_nondet_int();
  __CPROVER_assume(return_value >= -1);

#if !defined(__linux__) || defined(__GLIBC__)
  (void)*stream;
#else
  (void)*(char*)stream;
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fileno file must be open");
#endif

  return return_value;
}

/* FUNCTION: fputs */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fputs(const char *s, FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "fputs zero-termination of 1st argument");
#endif
  (void)*s;

  if(stream != stdout && stream != stderr)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fputs file must be open");
#endif

  return return_value;
}

/* FUNCTION: fflush */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fflush(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();
  (void)stream;

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  if(stream)
    __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                     "fflush file must be open");
#endif

  return return_value;
}

/* FUNCTION: fpurge */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fpurge(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

  if(stream != stdin && stream != stdout && stream != stderr)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fpurge file must be open");
#endif

  return return_value;
}

/* FUNCTION: fgetc */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fgetc(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

  // it's a byte or EOF (-1)
  __CPROVER_assume(return_value>=-1 && return_value<=255);

  __CPROVER_input("fgetc", return_value);

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fgetc file must be open");
#endif

  return return_value;
}

/* FUNCTION: getc */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int getc(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "getc file must be open");
#endif

  // It's a byte or EOF, which we fix to -1.
  __CPROVER_assume(return_value>=-1 && return_value<=255);

  __CPROVER_input("getc", return_value);

  return return_value;
}

/* FUNCTION: getchar */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int getchar()
{
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();
  // it's a byte or EOF
  __CPROVER_assume(return_value>=-1 && return_value<=255);
  __CPROVER_input("getchar", return_value);
  return return_value;
}

/* FUNCTION: getw */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int getw(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "getw file must be open");
#endif

  __CPROVER_input("getw", return_value);

  // it's any int, no restriction
  return return_value;
}

/* FUNCTION: fseek */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int fseek(FILE *stream, long offset, int whence)
{
  __CPROVER_HIDE:;
  int return_value=__VERIFIER_nondet_int();

#if !defined(__linux__) || defined(__GLIBC__)
  (void)*stream;
#else
  (void)*(char*)stream;
#endif
  (void)offset;
  (void)whence;

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fseek file must be open");
#endif

  return return_value;
}

/* FUNCTION: ftell */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

long __VERIFIER_nondet_long();

inline long ftell(FILE *stream)
{
  __CPROVER_HIDE:;
  long return_value=__VERIFIER_nondet_long();

#if !defined(__linux__) || defined(__GLIBC__)
  (void)*stream;
#else
  (void)*(char*)stream;
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "ftell file must be open");
#endif

  return return_value;
}

/* FUNCTION: rewind */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

void rewind(FILE *stream)
{
__CPROVER_HIDE:

#if !defined(__linux__) || defined(__GLIBC__)
  (void)*stream;
#else
  (void)*(char*)stream;
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "rewind file must be open");
#endif
}

/* FUNCTION: fwrite */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

size_t __VERIFIER_nondet_size_t();

size_t fwrite(
  const void *ptr,
  size_t size,
  size_t nitems,
  FILE *stream)
{
  __CPROVER_HIDE:;
  (void)*(char*)ptr;
  (void)size;

  if(stream != stdout && stream != stderr)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fwrite file must be open");
#endif

  size_t nwrite=__VERIFIER_nondet_size_t();
  __CPROVER_assume(nwrite<=nitems);
  return nwrite;
}

/* FUNCTION: perror */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

void perror(const char *s)
{
  __CPROVER_HIDE:;
  if(s!=0)
  {
    #ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_assert(__CPROVER_is_zero_string(s), "perror zero-termination");
    #endif
    // should go to stderr
    if(s[0]!=0)
      __CPROVER_printf("%s: ", s);
  }

  // TODO: print errno error
}

/* FUNCTION: fscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int fscanf(FILE *restrict stream, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfscanf(stream, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: scanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int scanf(const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfscanf(stdin, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: sscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int sscanf(const char *restrict s, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vsscanf(s, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: vfscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int vfscanf(FILE *restrict stream, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result=__VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

  (void)*format;
  (void)arg;

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "vfscanf file must be open");
#endif

  return result;
}

/* FUNCTION: vscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int vscanf(const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  return vfscanf(stdin, format, arg);
}

/* FUNCTION: vsscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int vsscanf(const char *restrict s, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result=__VERIFIER_nondet_int();
  (void)*s;
  (void)*format;
  (void)arg;
  return result;
}

/* FUNCTION: printf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int printf(const char *format, ...)
{
__CPROVER_HIDE:;
  int result = __VERIFIER_nondet_int();
  va_list list;
  va_start(list, format);
  __CPROVER_printf(format, list);
  va_end(list);
  return result;
}

/* FUNCTION: fprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int fprintf(FILE *stream, const char *restrict format, ...)
{
  __CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfprintf(stream, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: vfprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int vfprintf(FILE *stream, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;

  int result=__VERIFIER_nondet_int();

  if(stream != stdout && stream != stderr)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

  (void)*format;
  (void)arg;

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "vfprintf file must be open");
#endif

  return result;
}

/* FUNCTION: vasprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

char __VERIFIER_nondet_char();
int __VERIFIER_nondet_int();

inline int vasprintf(char **ptr, const char *fmt, va_list ap)
{
  (void)*fmt;
  (void)ap;

  int result_buffer_size=__VERIFIER_nondet_int();
  if(result_buffer_size<=0)
    return -1;

  *ptr=malloc(result_buffer_size);
  int i=0;
  for( ; i<result_buffer_size; ++i)
  {
    char c=__VERIFIER_nondet_char();
    (*ptr)[i]=c;
    if(c=='\0')
      break;
  }

  __CPROVER_assume(i<result_buffer_size);

  return i;
}

/* FUNCTION: __acrt_iob_func */

#ifdef _WIN32

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

inline FILE *__acrt_iob_func(unsigned fd)
{
  static FILE stdin_file;
  static FILE stdout_file;
  static FILE stderr_file;

  switch(fd)
  {
  case 0:
    return &stdin_file;
  case 1:
    return &stdout_file;
  case 2:
    return &stderr_file;
  default:
    return (FILE *)0;
  }
}

#endif

/* FUNCTION: __stdio_common_vfprintf */

#ifdef _WIN32

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

inline int __stdio_common_vfprintf(
  unsigned __int64 options,
  FILE *stream,
  char const *format,
  _locale_t locale,
  va_list args)
{
  (void)options;
  (void)locale;

  if(stream == __acrt_iob_func(1))
    __CPROVER_printf(format, args);
  return 0;
}

#endif
