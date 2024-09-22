
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

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

int putchar(int c)
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

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

int puts(const char *s)
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
void fclose_cleanup(void *stream)
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
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
FILE *fopen64(const char *filename, const char *mode);

FILE *fopen(const char *filename, const char *mode)
{
__CPROVER_HIDE:;
  return fopen64(filename, mode);
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
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

#ifdef __APPLE__
FILE *_fopen(const char *filename, const char *mode)
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

/* FUNCTION: fopen64 */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#  include <stdlib.h>
#  define __CPROVER_STDLIB_H_INCLUDED
#endif

void fclose_cleanup(void *stream);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

FILE *fopen64(const char *filename, const char *mode)
{
__CPROVER_HIDE:;
  (void)*filename;
  (void)*mode;
#ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(
    __CPROVER_is_zero_string(filename),
    "fopen zero-termination of 1st argument");
  __CPROVER_assert(
    __CPROVER_is_zero_string(mode), "fopen zero-termination of 2nd argument");
#endif

  FILE *fopen_result;

  __CPROVER_bool fopen_error = __VERIFIER_nondet___CPROVER_bool();

#if !defined(__linux__) || defined(__GLIBC__)
  fopen_result = fopen_error ? NULL : malloc(sizeof(FILE));
#else
  // libraries need to expose the definition of FILE; this is the
  // case for musl
  fopen_result = fopen_error ? NULL : malloc(sizeof(int));
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(fopen_result, "open");
  __CPROVER_cleanup(fopen_result, fclose_cleanup);
#endif

  return fopen_result;
}

/* FUNCTION: freopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

FILE *freopen64(const char *filename, const char *mode, FILE *f);

FILE *freopen(const char *filename, const char *mode, FILE *f)
{
__CPROVER_HIDE:;
  return freopen64(filename, mode, f);
}

/* FUNCTION: freopen64 */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

FILE *freopen64(const char *filename, const char *mode, FILE *f)
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

int __VERIFIER_nondet_int(void);

int fclose(FILE *stream)
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

FILE *fdopen(int handle, const char *mode)
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
FILE *_fdopen(int handle, const char *mode)
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

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

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

/* FUNCTION: __fgets_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

char *__fgets_chk(char *str, __CPROVER_size_t bufsize, int size, FILE *stream)
{
__CPROVER_HIDE:;
  (void)bufsize;
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();

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
  __CPROVER_assert(
    __CPROVER_get_must(stream, "open"), "fgets file must be open");
#endif

#ifdef __CPROVER_STRING_ABSTRACTION
  int resulting_size;
  __CPROVER_assert(
    __CPROVER_buffer_size(str) >= size, "buffer-overflow in fgets");
  if(size > 0)
  {
    __CPROVER_assume(resulting_size < size);
    __CPROVER_is_zero_string(str) = !error;
    __CPROVER_zero_string_length(str) = resulting_size;
  }
#else
  if(size > 0)
  {
    int str_length = __VERIFIER_nondet_int();
    __CPROVER_assume(str_length >= 0 && str_length < size);
    __CPROVER_precondition(__CPROVER_w_ok(str, size), "fgets buffer writable");
    char contents_nondet[str_length];
    __CPROVER_array_replace(str, contents_nondet);
    if(!error)
      str[str_length] = '\0';
  }
#endif

  return error ? 0 : str;
}

/* FUNCTION: fread */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

char __VERIFIER_nondet_char(void);
size_t __VERIFIER_nondet_size_t(void);

size_t fread(void *ptr, size_t size, size_t nitems, FILE *stream)
{
__CPROVER_HIDE:;
  size_t bytes_read = __VERIFIER_nondet_size_t();
  size_t upper_bound = nitems * size;
  __CPROVER_assume(bytes_read <= upper_bound);

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

  for(size_t i = 0; i < bytes_read && i < upper_bound; i++)
  {
    ((char *)ptr)[i] = __VERIFIER_nondet_char();
  }

  return bytes_read / size;
}

/* FUNCTION: __fread_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

char __VERIFIER_nondet_char(void);
size_t __VERIFIER_nondet_size_t(void);

size_t
__fread_chk(void *ptr, size_t ptrlen, size_t size, size_t nitems, FILE *stream)
{
__CPROVER_HIDE:;
  size_t bytes_read = __VERIFIER_nondet_size_t();
  size_t upper_bound = nitems * size;
  __CPROVER_assume(bytes_read <= upper_bound);

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(
    __CPROVER_get_must(stream, "open"), "fread file must be open");
#endif

  for(size_t i = 0; i < bytes_read && i < upper_bound && i < ptrlen; i++)
  {
    ((char *)ptr)[i] = __VERIFIER_nondet_char();
  }

  return bytes_read / size;
}

/* FUNCTION: feof */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int feof(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int ferror(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int fileno(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int fputs(const char *s, FILE *stream)
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

int __VERIFIER_nondet_int(void);

int fflush(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int fpurge(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int fgetc(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int getc(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int getchar(void)
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

int __VERIFIER_nondet_int(void);

int getw(FILE *stream)
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

int __VERIFIER_nondet_int(void);

int fseek(FILE *stream, long offset, int whence)
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

long __VERIFIER_nondet_long(void);

long ftell(FILE *stream)
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

size_t __VERIFIER_nondet_size_t(void);

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

#if !defined(__USE_ISOC99) || !defined(__REDIRECT)

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int fscanf(FILE *restrict stream, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfscanf(stream, format, list);
  va_end(list);
  return result;
}

#endif

/* FUNCTION: __isoc99_fscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __isoc99_fscanf(FILE *restrict stream, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result = vfscanf(stream, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: scanf */

#if !defined(__USE_ISOC99) || !defined(__REDIRECT)

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int scanf(const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfscanf(stdin, format, list);
  va_end(list);
  return result;
}

#endif

/* FUNCTION: __isoc99_scanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __isoc99_scanf(const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result = vfscanf(stdin, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: sscanf */

#if !defined(__USE_ISOC99) || !defined(__REDIRECT)

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int sscanf(const char *restrict s, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vsscanf(s, format, list);
  va_end(list);
  return result;
}

#endif

/* FUNCTION: __isoc99_sscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __isoc99_sscanf(const char *restrict s, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result = vsscanf(s, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: vfscanf */

#if !defined(__USE_ISOC99) || !defined(__REDIRECT)

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int __VERIFIER_nondet_int(void);

int vfscanf(FILE *restrict stream, const char *restrict format, va_list arg)
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
#  if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg.__stack) <
        __CPROVER_OBJECT_SIZE(arg.__stack))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#  else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg) <
        __CPROVER_OBJECT_SIZE(arg))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#  endif

#  ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "vfscanf file must be open");
#endif

  return result;
}

#endif

/* FUNCTION: __isoc99_vfscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __isoc99_vfscanf(
  FILE *restrict stream,
  const char *restrict format,
  va_list arg)
{
__CPROVER_HIDE:;
  int result = __VERIFIER_nondet_int();

  if(stream != stdin)
  {
#if !defined(__linux__) || defined(__GLIBC__)
    (void)*stream;
#else
    (void)*(char *)stream;
#endif
  }

  (void)*format;
#if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg.__stack) <
        __CPROVER_OBJECT_SIZE(arg.__stack))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg) <
        __CPROVER_OBJECT_SIZE(arg))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(
    __CPROVER_get_must(stream, "open"), "vfscanf file must be open");
#endif

  return result;
}

/* FUNCTION: __stdio_common_vfscanf */

#ifdef _WIN32

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int __VERIFIER_nondet_int(void);

int __stdio_common_vfscanf(
  unsigned __int64 options,
  FILE *stream,
  char const *format,
  _locale_t locale,
  va_list args)
{
  (void)options;
  (void)locale;

  int result = __VERIFIER_nondet_int();

  if(stream != stdin)
  {
    (void)*(char *)stream;
  }

  (void)*format;
#  if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(args.__stack) <
        __CPROVER_OBJECT_SIZE(args.__stack))
  {
    void *a = va_arg(args, void *);
    __CPROVER_havoc_object(a);
  }
#  else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(args) <
        __CPROVER_OBJECT_SIZE(args))
  {
    void *a = va_arg(args, void *);
    __CPROVER_havoc_object(a);
  }
#  endif

#  ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(
    __CPROVER_get_must(stream, "open"), "vfscanf file must be open");
#  endif

  return result;
}

#endif

/* FUNCTION: vscanf */

#if !defined(__USE_ISOC99) || !defined(__REDIRECT)

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int vscanf(const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  return vfscanf(stdin, format, arg);
}

#endif

/* FUNCTION: __isoc99_vscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __isoc99_vscanf(const char *restrict format, va_list arg)
{
__CPROVER_HIDE:;
  return vfscanf(stdin, format, arg);
}

/* FUNCTION: vsscanf */

#if !defined(__USE_ISOC99) || !defined(__REDIRECT)

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int __VERIFIER_nondet_int(void);

int vsscanf(const char *restrict s, const char *restrict format, va_list arg)
{
__CPROVER_HIDE:;
  int result = __VERIFIER_nondet_int();
  (void)*s;
  (void)*format;
#  if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg.__stack) <
        __CPROVER_OBJECT_SIZE(arg.__stack))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#  else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg) <
        __CPROVER_OBJECT_SIZE(arg))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#  endif

  return result;
}

#endif

/* FUNCTION: __isoc99_vsscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __isoc99_vsscanf(
  const char *restrict s,
  const char *restrict format,
  va_list arg)
{
__CPROVER_HIDE:;
  int result = __VERIFIER_nondet_int();
  (void)*s;
  (void)*format;
#if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg.__stack) <
        __CPROVER_OBJECT_SIZE(arg.__stack))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(arg) <
        __CPROVER_OBJECT_SIZE(arg))
  {
    void *a = va_arg(arg, void *);
    __CPROVER_havoc_object(a);
  }
#endif

  return result;
}

/* FUNCTION: __stdio_common_vsscanf */

#ifdef _WIN32

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

int __VERIFIER_nondet_int(void);

int __stdio_common_vsscanf(
  unsigned __int64 options,
  char const *s,
  size_t buffer_count,
  char const *format,
  _locale_t locale,
  va_list args)
{
  (void)options;
  (void)locale;

  int result = __VERIFIER_nondet_int();

  (void)*s;
  (void)*format;
#  if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(args.__stack) <
        __CPROVER_OBJECT_SIZE(args.__stack))
  {
    void *a = va_arg(args, void *);
    __CPROVER_havoc_object(a);
  }
#  else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(args) <
        __CPROVER_OBJECT_SIZE(args))
  {
    void *a = va_arg(args, void *);
    __CPROVER_havoc_object(a);
  }
#  endif

  return result;
}

#endif

/* FUNCTION: printf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int printf(const char *format, ...)
{
__CPROVER_HIDE:;
  int result = __VERIFIER_nondet_int();
  va_list list;
  va_start(list, format);
  __CPROVER_printf(format, list);
  va_end(list);
  return result;
}

/* FUNCTION: __printf_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __printf_chk(int flag, const char *format, ...)
{
__CPROVER_HIDE:;
  (void)flag;
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

int fprintf(FILE *stream, const char *restrict format, ...)
{
  __CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfprintf(stream, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: __fprintf_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __fprintf_chk(FILE *stream, int flag, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  (void)flag;
  va_list list;
  va_start(list, format);
  int result = vfprintf(stream, format, list);
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

int __VERIFIER_nondet_int(void);

int vfprintf(FILE *stream, const char *restrict format, va_list arg)
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

/* FUNCTION: __vfprintf_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int __vfprintf_chk(
  FILE *stream,
  int flag,
  const char *restrict format,
  va_list arg)
{
__CPROVER_HIDE:;
  (void)flag;

  int result = __VERIFIER_nondet_int();

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
  __CPROVER_assert(
    __CPROVER_get_must(stream, "open"), "vfprintf file must be open");
#endif

  return result;
}

/* FUNCTION: asprintf */

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

// declare here instead of relying on stdio.h as even those platforms that do
// have it at all may require _GNU_SOURCE to be set
int vasprintf(char **ptr, const char *fmt, va_list ap);

int asprintf(char **ptr, const char *fmt, ...)
{
  va_list list;
  va_start(list, fmt);
  int result = vasprintf(ptr, fmt, list);
  va_end(list);
  return result;
}

/* FUNCTION: dprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int dprintf(int fd, const char *restrict format, ...)
{
__CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result = vdprintf(fd, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: vdprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);

int vdprintf(int fd, const char *restrict format, va_list arg)
{
__CPROVER_HIDE:;

  int result = __VERIFIER_nondet_int();

  (void)fd;
  (void)*format;
  (void)arg;

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

char __VERIFIER_nondet_char(void);
int __VERIFIER_nondet_int(void);

int vasprintf(char **ptr, const char *fmt, va_list ap)
{
  (void)*fmt;
  (void)ap;

  int result_buffer_size=__VERIFIER_nondet_int();
  if(result_buffer_size<=0)
    return -1;

  *ptr=malloc(result_buffer_size);
  if(!*ptr)
    return -1;
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

/* FUNCTION: snprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

#undef snprintf

int snprintf(char *str, size_t size, const char *fmt, ...)
{
  va_list list;
  va_start(list, fmt);
  int result = vsnprintf(str, size, fmt, list);
  va_end(list);
  return result;
}

/* FUNCTION: __builtin___snprintf_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

int __builtin___vsnprintf_chk(
  char *str,
  size_t size,
  int flag,
  size_t bufsize,
  const char *fmt,
  va_list ap);

int __builtin___snprintf_chk(
  char *str,
  size_t size,
  int flag,
  size_t bufsize,
  const char *fmt,
  ...)
{
  va_list list;
  va_start(list, fmt);
  int result = __builtin___vsnprintf_chk(str, size, flag, bufsize, fmt, list);
  va_end(list);
  return result;
}

/* FUNCTION: vsnprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

#undef vsnprintf

char __VERIFIER_nondet_char(void);

int vsnprintf(char *str, size_t size, const char *fmt, va_list ap)
{
  (void)*fmt;

#if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(ap.__stack) <
        __CPROVER_OBJECT_SIZE(ap.__stack))

  {
    (void)va_arg(ap, int);
    __CPROVER_precondition(
      __CPROVER_POINTER_OBJECT(str) != __CPROVER_POINTER_OBJECT(ap.__stack),
      "vsnprintf object overlap");
  }
#else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(ap) <
        __CPROVER_OBJECT_SIZE(ap))

  {
    (void)va_arg(ap, int);
    __CPROVER_precondition(
      __CPROVER_POINTER_OBJECT(str) != __CPROVER_POINTER_OBJECT(ap),
      "vsnprintf object overlap");
  }
#endif

  size_t i = 0;
  for(; i < size; ++i)
  {
    char c = __VERIFIER_nondet_char();
    str[i] = c;
    if(c == '\0')
      break;
  }

  return i;
}

/* FUNCTION: __builtin___vsnprintf_chk */

#ifndef __CPROVER_STDIO_H_INCLUDED
#  include <stdio.h>
#  define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#  include <stdarg.h>
#  define __CPROVER_STDARG_H_INCLUDED
#endif

char __VERIFIER_nondet_char(void);

int __builtin___vsnprintf_chk(
  char *str,
  size_t size,
  int flag,
  size_t bufsize,
  const char *fmt,
  va_list ap)
{
  (void)flag;
  (void)bufsize;
  (void)*fmt;

#if(defined(__aarch64__) || defined(_M_ARM64)) && !defined(__APPLE__)
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(ap.__stack) <
        __CPROVER_OBJECT_SIZE(ap.__stack))

  {
    (void)va_arg(ap, int);
    __CPROVER_precondition(
      __CPROVER_POINTER_OBJECT(str) != __CPROVER_POINTER_OBJECT(ap.__stack),
      "vsnprintf object overlap");
  }
#else
  while((__CPROVER_size_t)__CPROVER_POINTER_OFFSET(ap) <
        __CPROVER_OBJECT_SIZE(ap))

  {
    (void)va_arg(ap, int);
    __CPROVER_precondition(
      __CPROVER_POINTER_OBJECT(str) != __CPROVER_POINTER_OBJECT(ap),
      "vsnprintf object overlap");
  }
#endif

  size_t i = 0;
  for(; i < size; ++i)
  {
    char c = __VERIFIER_nondet_char();
    str[i] = c;
    if(c == '\0')
      break;
  }

  return i;
}

/* FUNCTION: __acrt_iob_func */

#ifdef _WIN32

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

FILE *__acrt_iob_func(unsigned fd)
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

int __stdio_common_vfprintf(
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

/* FUNCTION: __stdio_common_vsprintf */

#ifdef _WIN32

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

#  ifndef __CPROVER_STDARG_H_INCLUDED
#    include <stdarg.h>
#    define __CPROVER_STDARG_H_INCLUDED
#  endif

char __VERIFIER_nondet_char(void);

int __stdio_common_vsprintf(
  unsigned __int64 options,
  char *str,
  size_t size,
  char const *fmt,
  _locale_t locale,
  va_list args)
{
  (void)options;
  (void)*fmt;
  (void)locale;
  (void)args;

  size_t i = 0;
  for(; i < size; ++i)
  {
    char c = __VERIFIER_nondet_char();
    str[i] = c;
    if(c == '\0')
      break;
  }

  return i;
}

#endif

/* FUNCTION: __srget */

#ifdef __FreeBSD__

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

int __VERIFIER_nondet_int(void);

int __srget(FILE *stream)
{
  (void)*stream;

  // FreeBSD's implementation returns a character or EOF; __VERIFIER_nondet_int
  // will capture all these options
  return __VERIFIER_nondet_int();
}

#endif

/* FUNCTION: __swbuf */

#ifdef __FreeBSD__

#  ifndef __CPROVER_STDIO_H_INCLUDED
#    include <stdio.h>
#    define __CPROVER_STDIO_H_INCLUDED
#  endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

int __swbuf(int c, FILE *stream)
{
  (void)c;
  (void)*stream;

  // FreeBSD's implementation returns `c` or or EOF in case writing failed; we
  // just non-deterministically choose between these
  if(__VERIFIER_nondet___CPROVER_bool())
    return EOF;
  else
    return c;
}

#endif
