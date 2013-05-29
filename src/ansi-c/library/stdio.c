
/* FUNCTION: putchar */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int putchar(int c)
{
  _Bool error;
  __CPROVER_HIDE: printf("%c", c);
  return (error?-1:c);
}

/* FUNCTION: puts */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int puts(const char *s)
{
  __CPROVER_HIDE:;
  _Bool error;
  int ret;
  printf("%s\n", s);
  if(error) ret=-1; else __CPROVER_assume(ret>=0);
  return ret;
}

/* FUNCTION: fopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

inline FILE *fopen(const char *filename, const char *mode)
{
  __CPROVER_HIDE:;
  (void)*filename;
  (void)*mode;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(filename), "fopen zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(mode), "fopen zero-termination of 2nd argument");
  #endif

  FILE *f=malloc(sizeof(FILE));

  return f;
}

/* FUNCTION: fclose */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fclose(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
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

  FILE *f=malloc(sizeof(FILE));

  return f;
}

/* FUNCTION: fgets */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline char *fgets(char *str, int size, FILE *stream)
{
  __CPROVER_HIDE:;
  _Bool error;

  (void)size;
  (void)*stream;
  #ifdef __CPROVER_STRING_ABSTRACTION
  int resulting_size;
  __CPROVER_assert(__CPROVER_buffer_size(str)>=size, "buffer-overflow in fgets");
  if(size>0)
  {
    __CPROVER_assume(resulting_size<size);
    __CPROVER_is_zero_string(str)=!error;
    __CPROVER_zero_string_length(str)=resulting_size;
  }
  #endif

  return error?0:str;
}

/* FUNCTION: fread */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline size_t fread(
  void *ptr,
  size_t size,
  size_t nitems,
  FILE *stream)
{
  __CPROVER_HIDE:;
  size_t nread;
  size_t bytes=nread*size;
  size_t i;
  __CPROVER_assume(nread<=nitems);

  (void)*stream;

  for(i=0; i<bytes; i++)
  {
    char nondet_char;
    ((char *)ptr)[i]=nondet_char;
  }

  return nread;
}

/* FUNCTION: feof */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int feof(FILE *stream)
{
  // just return nondet
  int return_value;
  (void)*stream;
  return return_value;
}

/* FUNCTION: ferror */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int ferror(FILE *stream)
{
  // just return nondet
  int return_value;
  (void)*stream;
  return return_value;
}

/* FUNCTION: fileno */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fileno(FILE *stream)
{
  // just return nondet
  int return_value;
  (void)*stream;
  return return_value;
}

/* FUNCTION: fputs */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int fputs(const char *s, FILE *stream)
{
  // just return nondet
  int return_value;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "fputs zero-termination of 1st argument");
  #endif
  (void)*s;
  (void)*stream;
  return return_value;
}

/* FUNCTION: fflush */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int fflush(FILE *stream)
{
  // just return nondet
  int return_value;
  (void)*stream;
  return return_value;
}

/* FUNCTION: fpurge */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int fpurge(FILE *stream)
{
  // just return nondet
  int return_value;
  (void)*stream;
  return return_value;
}

/* FUNCTION: read */

#ifndef __CPROVER_UNISTD_H_INCLUDED
#include <unistd.h>
#define __CPROVER_UNISTD_H_INCLUDED
#endif

inline ssize_t read(int fildes, void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  ssize_t nread;
  size_t i;
  (void)fildes;
  __CPROVER_assume((size_t)nread<=nbyte);

  for(i=0; i<nbyte; i++)
  {
    char nondet_char;
    ((char *)buf)[i]=nondet_char;
  }

  return nread;
}

/* FUNCTION: fgetc */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fgetc(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
  // it's a byte or EOF (-1)
  __CPROVER_assume(return_value>=-1 && return_value<=255);
  return return_value;
}

/* FUNCTION: getc */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int getc(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
  // it's a byte or EOF
  __CPROVER_assume(return_value>=-1 && return_value<=255);
  return return_value;
}

/* FUNCTION: getchar */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int getchar()
{
  __CPROVER_HIDE:;
  int return_value;
  // it's a byte or EOF
  __CPROVER_assume(return_value>=-1 && return_value<=255);
  return return_value;
}

/* FUNCTION: getw */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int getw(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
  // it's any int, no restriction
  return return_value;
}

/* FUNCTION: fseek */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fseek(FILE *stream, long offset, int whence)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
  (void)offset;
  (void)whence;
  return return_value;
}

/* FUNCTION: ftell */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

long ftell(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
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
  (void)*stream;
}

/* FUNCTION: fwrite */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

size_t fwrite(
  const void *ptr,
  size_t size,
  size_t nitems,
  FILE *stream)
{
  __CPROVER_HIDE:;
  (void)*(char*)ptr;
  (void)size;
  (void)*stream;
  size_t nwrite;
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
      printf("%s: ", s);
  }
  
  // TODO: print errno error
}

/* FUNCTION: fscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int fscanf(FILE *restrict stream, const char *restrict format, ...)
{
  __CPOVER_HIDE:;
  __builtin_va_list list;
  __builtin_va_start(list, format);
  int result=vfscanf(stream, format, list);
  __builtin_va_end(list);
  return result;
}

/* FUNCTION: scanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int scanf(const char *restrict format, ...)
{
  __CPOVER_HIDE:;
  __builtin_va_list list;
  __builtin_va_start(list, format);
  int result=vfscanf(stdin, format, list);
  __builtin_va_end(list);
  return result;
}

/* FUNCTION: sscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int sscanf(const char *restrict s, const char *restrict format, ...)
{
  __CPOVER_HIDE:;
  __builtin_va_list list;
  __builtin_va_start(list, format);
  int result=vsscanf(s, format, list);
  __builtin_va_end(list);
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

int vfscanf(FILE *restrict stream, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result;
  (void)*stream;
  (void)*format;
  (void)arg;
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

int vscanf(const char *restrict format, va_list arg)
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

int vsscanf(const char *restrict s, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result;
  (void)*s;
  (void)*format;
  (void)arg;
  return result;
}

/* FUNCTION: fprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

int fprintf(FILE *stream, const char *restrict format, ...)
{
  __CPROVER_HIDE:;
  __builtin_va_list list;
  __builtin_va_start(list, format);
  int result=vfprintf(stream, format, list);
  __builtin_va_end(list);
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

int vfprintf(FILE *stream, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result;
  (void)*stream;
  (void)*format;
  (void)arg;
  return result;
}

