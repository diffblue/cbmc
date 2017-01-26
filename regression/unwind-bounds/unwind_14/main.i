# 1 "main.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "main.c"
# 10 "main.c"
# 1 "/home/daniel/s/r_software/csmith-2.1.0/runtime/csmith.h" 1
# 40 "/home/daniel/s/r_software/csmith-2.1.0/runtime/csmith.h"
# 1 "/usr/include/string.h" 1 3 4
# 25 "/usr/include/string.h" 3 4
# 1 "/usr/include/features.h" 1 3 4
# 364 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 1 3 4
# 402 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 403 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 2 3 4
# 365 "/usr/include/features.h" 2 3 4
# 388 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 1 3 4
# 10 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs-64.h" 1 3 4
# 11 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 2 3 4
# 389 "/usr/include/features.h" 2 3 4
# 26 "/usr/include/string.h" 2 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stddef.h" 1 3 4
# 212 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stddef.h" 3 4
typedef long unsigned int size_t;
# 33 "/usr/include/string.h" 2 3 4
# 44 "/usr/include/string.h" 3 4


extern void *memcpy (void *__restrict __dest, const void *__restrict __src,
       size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void *memmove (void *__dest, const void *__src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));






extern void *memccpy (void *__restrict __dest, const void *__restrict __src,
        int __c, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));





extern void *memset (void *__s, int __c, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int memcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 96 "/usr/include/string.h" 3 4
extern void *memchr (const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));


# 127 "/usr/include/string.h" 3 4


extern char *strcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern char *strncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern char *strcat (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern char *strncat (char *__restrict __dest, const char *__restrict __src,
        size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strcmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));

extern int strncmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strcoll (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));

extern size_t strxfrm (char *__restrict __dest,
         const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));






# 1 "/usr/include/xlocale.h" 1 3 4
# 27 "/usr/include/xlocale.h" 3 4
typedef struct __locale_struct
{

  struct __locale_data *__locales[13];


  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;


  const char *__names[13];
} *__locale_t;


typedef __locale_t locale_t;
# 164 "/usr/include/string.h" 2 3 4


extern int strcoll_l (const char *__s1, const char *__s2, __locale_t __l)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));

extern size_t strxfrm_l (char *__dest, const char *__src, size_t __n,
    __locale_t __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));




extern char *strdup (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));






extern char *strndup (const char *__string, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
# 210 "/usr/include/string.h" 3 4

# 235 "/usr/include/string.h" 3 4
extern char *strchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 262 "/usr/include/string.h" 3 4
extern char *strrchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));


# 281 "/usr/include/string.h" 3 4



extern size_t strcspn (const char *__s, const char *__reject)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern size_t strspn (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 314 "/usr/include/string.h" 3 4
extern char *strpbrk (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 341 "/usr/include/string.h" 3 4
extern char *strstr (const char *__haystack, const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strtok (char *__restrict __s, const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));




extern char *__strtok_r (char *__restrict __s,
    const char *__restrict __delim,
    char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));

extern char *strtok_r (char *__restrict __s, const char *__restrict __delim,
         char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
# 396 "/usr/include/string.h" 3 4


extern size_t strlen (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));





extern size_t strnlen (const char *__string, size_t __maxlen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));





extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));

# 426 "/usr/include/string.h" 3 4
extern int strerror_r (int __errnum, char *__buf, size_t __buflen) __asm__ ("" "__xpg_strerror_r") __attribute__ ((__nothrow__ , __leaf__))

                        __attribute__ ((__nonnull__ (2)));
# 444 "/usr/include/string.h" 3 4
extern char *strerror_l (int __errnum, __locale_t __l) __attribute__ ((__nothrow__ , __leaf__));





extern void __bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern void bcopy (const void *__src, void *__dest, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int bcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 488 "/usr/include/string.h" 3 4
extern char *index (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 516 "/usr/include/string.h" 3 4
extern char *rindex (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));




extern int ffs (int __i) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
# 533 "/usr/include/string.h" 3 4
extern int strcasecmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strncasecmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 556 "/usr/include/string.h" 3 4
extern char *strsep (char **__restrict __stringp,
       const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));


extern char *__stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));



extern char *__stpncpy (char *__restrict __dest,
   const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
# 643 "/usr/include/string.h" 3 4

# 41 "/home/daniel/s/r_software/csmith-2.1.0/runtime/csmith.h" 2


# 1 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h" 1
# 51 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/limits.h" 1 3 4
# 34 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/limits.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/syslimits.h" 1 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/limits.h" 1 3 4
# 168 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/limits.h" 3 4
# 1 "/usr/include/limits.h" 1 3 4
# 143 "/usr/include/limits.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 1 3 4
# 160 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/local_lim.h" 1 3 4
# 38 "/usr/include/x86_64-linux-gnu/bits/local_lim.h" 3 4
# 1 "/usr/include/linux/limits.h" 1 3 4
# 39 "/usr/include/x86_64-linux-gnu/bits/local_lim.h" 2 3 4
# 161 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 2 3 4
# 144 "/usr/include/limits.h" 2 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/posix2_lim.h" 1 3 4
# 148 "/usr/include/limits.h" 2 3 4
# 169 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/limits.h" 2 3 4
# 8 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/syslimits.h" 2 3 4
# 35 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include-fixed/limits.h" 2 3 4
# 52 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h" 2



# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stdint.h" 1 3 4
# 9 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stdint.h" 3 4
# 1 "/usr/include/stdint.h" 1 3 4
# 26 "/usr/include/stdint.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wchar.h" 1 3 4
# 27 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 28 "/usr/include/stdint.h" 2 3 4
# 36 "/usr/include/stdint.h" 3 4
typedef signed char int8_t;
typedef short int int16_t;
typedef int int32_t;

typedef long int int64_t;







typedef unsigned char uint8_t;
typedef unsigned short int uint16_t;

typedef unsigned int uint32_t;



typedef unsigned long int uint64_t;
# 65 "/usr/include/stdint.h" 3 4
typedef signed char int_least8_t;
typedef short int int_least16_t;
typedef int int_least32_t;

typedef long int int_least64_t;






typedef unsigned char uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int uint_least32_t;

typedef unsigned long int uint_least64_t;
# 90 "/usr/include/stdint.h" 3 4
typedef signed char int_fast8_t;

typedef long int int_fast16_t;
typedef long int int_fast32_t;
typedef long int int_fast64_t;
# 103 "/usr/include/stdint.h" 3 4
typedef unsigned char uint_fast8_t;

typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;
# 119 "/usr/include/stdint.h" 3 4
typedef long int intptr_t;


typedef unsigned long int uintptr_t;
# 134 "/usr/include/stdint.h" 3 4
typedef long int intmax_t;
typedef unsigned long int uintmax_t;
# 10 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stdint.h" 2 3 4
# 56 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h" 2



# 1 "/usr/include/assert.h" 1 3 4
# 66 "/usr/include/assert.h" 3 4



extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));




extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));



# 60 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h" 2
# 89 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h"
# 1 "/home/daniel/s/r_software/csmith-2.1.0/runtime/platform_generic.h" 1
# 40 "/home/daniel/s/r_software/csmith-2.1.0/runtime/platform_generic.h"
# 1 "/usr/include/stdio.h" 1 3 4
# 29 "/usr/include/stdio.h" 3 4




# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stddef.h" 1 3 4
# 34 "/usr/include/stdio.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/types.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 28 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;


typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;

typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;







typedef long int __quad_t;
typedef unsigned long int __u_quad_t;
# 121 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/typesizes.h" 1 3 4
# 122 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;

typedef int __daddr_t;
typedef int __key_t;


typedef int __clockid_t;


typedef void * __timer_t;


typedef long int __blksize_t;




typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;


typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;


typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;


typedef long int __fsword_t;

typedef long int __ssize_t;


typedef long int __syscall_slong_t;

typedef unsigned long int __syscall_ulong_t;



typedef __off64_t __loff_t;
typedef __quad_t *__qaddr_t;
typedef char *__caddr_t;


typedef long int __intptr_t;


typedef unsigned int __socklen_t;
# 36 "/usr/include/stdio.h" 2 3 4
# 44 "/usr/include/stdio.h" 3 4
struct _IO_FILE;



typedef struct _IO_FILE FILE;





# 64 "/usr/include/stdio.h" 3 4
typedef struct _IO_FILE __FILE;
# 74 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/libio.h" 1 3 4
# 31 "/usr/include/libio.h" 3 4
# 1 "/usr/include/_G_config.h" 1 3 4
# 15 "/usr/include/_G_config.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stddef.h" 1 3 4
# 16 "/usr/include/_G_config.h" 2 3 4




# 1 "/usr/include/wchar.h" 1 3 4
# 82 "/usr/include/wchar.h" 3 4
typedef struct
{
  int __count;
  union
  {

    unsigned int __wch;



    char __wchb[4];
  } __value;
} __mbstate_t;
# 21 "/usr/include/_G_config.h" 2 3 4
typedef struct
{
  __off_t __pos;
  __mbstate_t __state;
} _G_fpos_t;
typedef struct
{
  __off64_t __pos;
  __mbstate_t __state;
} _G_fpos64_t;
# 32 "/usr/include/libio.h" 2 3 4
# 49 "/usr/include/libio.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stdarg.h" 1 3 4
# 40 "/usr/lib/gcc/x86_64-linux-gnu/4.9/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 50 "/usr/include/libio.h" 2 3 4
# 144 "/usr/include/libio.h" 3 4
struct _IO_jump_t; struct _IO_FILE;
# 154 "/usr/include/libio.h" 3 4
typedef void _IO_lock_t;





struct _IO_marker {
  struct _IO_marker *_next;
  struct _IO_FILE *_sbuf;



  int _pos;
# 177 "/usr/include/libio.h" 3 4
};


enum __codecvt_result
{
  __codecvt_ok,
  __codecvt_partial,
  __codecvt_error,
  __codecvt_noconv
};
# 245 "/usr/include/libio.h" 3 4
struct _IO_FILE {
  int _flags;




  char* _IO_read_ptr;
  char* _IO_read_end;
  char* _IO_read_base;
  char* _IO_write_base;
  char* _IO_write_ptr;
  char* _IO_write_end;
  char* _IO_buf_base;
  char* _IO_buf_end;

  char *_IO_save_base;
  char *_IO_backup_base;
  char *_IO_save_end;

  struct _IO_marker *_markers;

  struct _IO_FILE *_chain;

  int _fileno;



  int _flags2;

  __off_t _old_offset;



  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];



  _IO_lock_t *_lock;
# 293 "/usr/include/libio.h" 3 4
  __off64_t _offset;
# 302 "/usr/include/libio.h" 3 4
  void *__pad1;
  void *__pad2;
  void *__pad3;
  void *__pad4;
  size_t __pad5;

  int _mode;

  char _unused2[15 * sizeof (int) - 4 * sizeof (void *) - sizeof (size_t)];

};


typedef struct _IO_FILE _IO_FILE;


struct _IO_FILE_plus;

extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;
# 338 "/usr/include/libio.h" 3 4
typedef __ssize_t __io_read_fn (void *__cookie, char *__buf, size_t __nbytes);







typedef __ssize_t __io_write_fn (void *__cookie, const char *__buf,
     size_t __n);







typedef int __io_seek_fn (void *__cookie, __off64_t *__pos, int __w);


typedef int __io_close_fn (void *__cookie);
# 390 "/usr/include/libio.h" 3 4
extern int __underflow (_IO_FILE *);
extern int __uflow (_IO_FILE *);
extern int __overflow (_IO_FILE *, int);
# 434 "/usr/include/libio.h" 3 4
extern int _IO_getc (_IO_FILE *__fp);
extern int _IO_putc (int __c, _IO_FILE *__fp);
extern int _IO_feof (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ferror (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));

extern int _IO_peekc_locked (_IO_FILE *__fp);





extern void _IO_flockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern void _IO_funlockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ftrylockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
# 464 "/usr/include/libio.h" 3 4
extern int _IO_vfscanf (_IO_FILE * __restrict, const char * __restrict,
   __gnuc_va_list, int *__restrict);
extern int _IO_vfprintf (_IO_FILE *__restrict, const char *__restrict,
    __gnuc_va_list);
extern __ssize_t _IO_padn (_IO_FILE *, int, __ssize_t);
extern size_t _IO_sgetn (_IO_FILE *, void *, size_t);

extern __off64_t _IO_seekoff (_IO_FILE *, __off64_t, int, int);
extern __off64_t _IO_seekpos (_IO_FILE *, __off64_t, int);

extern void _IO_free_backup_area (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
# 75 "/usr/include/stdio.h" 2 3 4




typedef __gnuc_va_list va_list;
# 90 "/usr/include/stdio.h" 3 4
typedef __off_t off_t;
# 102 "/usr/include/stdio.h" 3 4
typedef __ssize_t ssize_t;







typedef _G_fpos_t fpos_t;




# 164 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdio_lim.h" 1 3 4
# 165 "/usr/include/stdio.h" 2 3 4



extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;







extern int remove (const char *__filename) __attribute__ ((__nothrow__ , __leaf__));

extern int rename (const char *__old, const char *__new) __attribute__ ((__nothrow__ , __leaf__));




extern int renameat (int __oldfd, const char *__old, int __newfd,
       const char *__new) __attribute__ ((__nothrow__ , __leaf__));








extern FILE *tmpfile (void) ;
# 209 "/usr/include/stdio.h" 3 4
extern char *tmpnam (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;





extern char *tmpnam_r (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;
# 227 "/usr/include/stdio.h" 3 4
extern char *tempnam (const char *__dir, const char *__pfx)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;








extern int fclose (FILE *__stream);




extern int fflush (FILE *__stream);

# 252 "/usr/include/stdio.h" 3 4
extern int fflush_unlocked (FILE *__stream);
# 266 "/usr/include/stdio.h" 3 4






extern FILE *fopen (const char *__restrict __filename,
      const char *__restrict __modes) ;




extern FILE *freopen (const char *__restrict __filename,
        const char *__restrict __modes,
        FILE *__restrict __stream) ;
# 295 "/usr/include/stdio.h" 3 4

# 306 "/usr/include/stdio.h" 3 4
extern FILE *fdopen (int __fd, const char *__modes) __attribute__ ((__nothrow__ , __leaf__)) ;
# 319 "/usr/include/stdio.h" 3 4
extern FILE *fmemopen (void *__s, size_t __len, const char *__modes)
  __attribute__ ((__nothrow__ , __leaf__)) ;




extern FILE *open_memstream (char **__bufloc, size_t *__sizeloc) __attribute__ ((__nothrow__ , __leaf__)) ;






extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));



extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
      int __modes, size_t __n) __attribute__ ((__nothrow__ , __leaf__));





extern void setbuffer (FILE *__restrict __stream, char *__restrict __buf,
         size_t __size) __attribute__ ((__nothrow__ , __leaf__));


extern void setlinebuf (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));








extern int fprintf (FILE *__restrict __stream,
      const char *__restrict __format, ...);




extern int printf (const char *__restrict __format, ...);

extern int sprintf (char *__restrict __s,
      const char *__restrict __format, ...) __attribute__ ((__nothrow__));





extern int vfprintf (FILE *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg);




extern int vprintf (const char *__restrict __format, __gnuc_va_list __arg);

extern int vsprintf (char *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg) __attribute__ ((__nothrow__));





extern int snprintf (char *__restrict __s, size_t __maxlen,
       const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 4)));

extern int vsnprintf (char *__restrict __s, size_t __maxlen,
        const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 0)));

# 412 "/usr/include/stdio.h" 3 4
extern int vdprintf (int __fd, const char *__restrict __fmt,
       __gnuc_va_list __arg)
     __attribute__ ((__format__ (__printf__, 2, 0)));
extern int dprintf (int __fd, const char *__restrict __fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));








extern int fscanf (FILE *__restrict __stream,
     const char *__restrict __format, ...) ;




extern int scanf (const char *__restrict __format, ...) ;

extern int sscanf (const char *__restrict __s,
     const char *__restrict __format, ...) __attribute__ ((__nothrow__ , __leaf__));
# 443 "/usr/include/stdio.h" 3 4
extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf")

                               ;
extern int scanf (const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf")
                              ;
extern int sscanf (const char *__restrict __s, const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__ , __leaf__))

                      ;
# 463 "/usr/include/stdio.h" 3 4








extern int vfscanf (FILE *__restrict __s, const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;





extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;


extern int vsscanf (const char *__restrict __s,
      const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
# 494 "/usr/include/stdio.h" 3 4
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vfscanf")



     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vscanf")

     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vsscanf") __attribute__ ((__nothrow__ , __leaf__))



     __attribute__ ((__format__ (__scanf__, 2, 0)));
# 522 "/usr/include/stdio.h" 3 4









extern int fgetc (FILE *__stream);
extern int getc (FILE *__stream);





extern int getchar (void);

# 550 "/usr/include/stdio.h" 3 4
extern int getc_unlocked (FILE *__stream);
extern int getchar_unlocked (void);
# 561 "/usr/include/stdio.h" 3 4
extern int fgetc_unlocked (FILE *__stream);











extern int fputc (int __c, FILE *__stream);
extern int putc (int __c, FILE *__stream);





extern int putchar (int __c);

# 594 "/usr/include/stdio.h" 3 4
extern int fputc_unlocked (int __c, FILE *__stream);







extern int putc_unlocked (int __c, FILE *__stream);
extern int putchar_unlocked (int __c);






extern int getw (FILE *__stream);


extern int putw (int __w, FILE *__stream);








extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     ;
# 638 "/usr/include/stdio.h" 3 4
extern char *gets (char *__s) __attribute__ ((__deprecated__));


# 665 "/usr/include/stdio.h" 3 4
extern __ssize_t __getdelim (char **__restrict __lineptr,
          size_t *__restrict __n, int __delimiter,
          FILE *__restrict __stream) ;
extern __ssize_t getdelim (char **__restrict __lineptr,
        size_t *__restrict __n, int __delimiter,
        FILE *__restrict __stream) ;







extern __ssize_t getline (char **__restrict __lineptr,
       size_t *__restrict __n,
       FILE *__restrict __stream) ;








extern int fputs (const char *__restrict __s, FILE *__restrict __stream);





extern int puts (const char *__s);






extern int ungetc (int __c, FILE *__stream);






extern size_t fread (void *__restrict __ptr, size_t __size,
       size_t __n, FILE *__restrict __stream) ;




extern size_t fwrite (const void *__restrict __ptr, size_t __size,
        size_t __n, FILE *__restrict __s);

# 737 "/usr/include/stdio.h" 3 4
extern size_t fread_unlocked (void *__restrict __ptr, size_t __size,
         size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite_unlocked (const void *__restrict __ptr, size_t __size,
          size_t __n, FILE *__restrict __stream);








extern int fseek (FILE *__stream, long int __off, int __whence);




extern long int ftell (FILE *__stream) ;




extern void rewind (FILE *__stream);

# 773 "/usr/include/stdio.h" 3 4
extern int fseeko (FILE *__stream, __off_t __off, int __whence);




extern __off_t ftello (FILE *__stream) ;
# 792 "/usr/include/stdio.h" 3 4






extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos);




extern int fsetpos (FILE *__stream, const fpos_t *__pos);
# 815 "/usr/include/stdio.h" 3 4

# 824 "/usr/include/stdio.h" 3 4


extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));

extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;




extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;








extern void perror (const char *__s);






# 1 "/usr/include/x86_64-linux-gnu/bits/sys_errlist.h" 1 3 4
# 26 "/usr/include/x86_64-linux-gnu/bits/sys_errlist.h" 3 4
extern int sys_nerr;
extern const char *const sys_errlist[];
# 854 "/usr/include/stdio.h" 2 3 4




extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;




extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
# 872 "/usr/include/stdio.h" 3 4
extern FILE *popen (const char *__command, const char *__modes) ;





extern int pclose (FILE *__stream);





extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__));
# 912 "/usr/include/stdio.h" 3 4
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));



extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;


extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
# 942 "/usr/include/stdio.h" 3 4

# 41 "/home/daniel/s/r_software/csmith-2.1.0/runtime/platform_generic.h" 2


static void
platform_main_begin(void)
{

}

static void
platform_main_end(uint32_t crc, int flag)
{



 printf ("checksum = %X\n", crc);
# 117 "/home/daniel/s/r_software/csmith-2.1.0/runtime/platform_generic.h"
}
# 90 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h" 2
# 100 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h"
# 1 "/home/daniel/s/r_software/csmith-2.1.0/runtime/safe_math.h" 1
# 13 "/home/daniel/s/r_software/csmith-2.1.0/runtime/safe_math.h"
static int8_t
(safe_unary_minus_func_int8_t_s)(int8_t si )
{
 
  return






    -si;
}

static int8_t
(safe_add_func_int8_t_s_s)(int8_t si1, int8_t si2 )
{
 
  return






    (si1 + si2);
}

static int8_t
(safe_sub_func_int8_t_s_s)(int8_t si1, int8_t si2 )
{
 
  return






    (si1 - si2);
}

static int8_t
(safe_mul_func_int8_t_s_s)(int8_t si1, int8_t si2 )
{
 
  return






    si1 * si2;
}

static int8_t
(safe_mod_func_int8_t_s_s)(int8_t si1, int8_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-128)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 % si2);
}

static int8_t
(safe_div_func_int8_t_s_s)(int8_t si1, int8_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-128)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 / si2);
}

static int8_t
(safe_lshift_func_int8_t_s_s)(int8_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > ((127) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static int8_t
(safe_lshift_func_int8_t_s_u)(int8_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32) || (left > ((127) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static int8_t
(safe_rshift_func_int8_t_s_s)(int8_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))?
    ((left)) :

    (left >> ((int)right));
}

static int8_t
(safe_rshift_func_int8_t_s_u)(int8_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32)) ?
    ((left)) :

    (left >> ((unsigned int)right));
}



static int16_t
(safe_unary_minus_func_int16_t_s)(int16_t si )
{
 
  return






    -si;
}

static int16_t
(safe_add_func_int16_t_s_s)(int16_t si1, int16_t si2 )
{
 
  return






    (si1 + si2);
}

static int16_t
(safe_sub_func_int16_t_s_s)(int16_t si1, int16_t si2 )
{
 
  return






    (si1 - si2);
}

static int16_t
(safe_mul_func_int16_t_s_s)(int16_t si1, int16_t si2 )
{
 
  return






    si1 * si2;
}

static int16_t
(safe_mod_func_int16_t_s_s)(int16_t si1, int16_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-32767-1)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 % si2);
}

static int16_t
(safe_div_func_int16_t_s_s)(int16_t si1, int16_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-32767-1)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 / si2);
}

static int16_t
(safe_lshift_func_int16_t_s_s)(int16_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > ((32767) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static int16_t
(safe_lshift_func_int16_t_s_u)(int16_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32) || (left > ((32767) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static int16_t
(safe_rshift_func_int16_t_s_s)(int16_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))?
    ((left)) :

    (left >> ((int)right));
}

static int16_t
(safe_rshift_func_int16_t_s_u)(int16_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32)) ?
    ((left)) :

    (left >> ((unsigned int)right));
}



static int32_t
(safe_unary_minus_func_int32_t_s)(int32_t si )
{
 
  return


    (si==(-2147483647-1)) ?
    ((si)) :


    -si;
}

static int32_t
(safe_add_func_int32_t_s_s)(int32_t si1, int32_t si2 )
{
 
  return


    (((si1>0) && (si2>0) && (si1 > ((2147483647)-si2))) || ((si1<0) && (si2<0) && (si1 < ((-2147483647-1)-si2)))) ?
    ((si1)) :


    (si1 + si2);
}

static int32_t
(safe_sub_func_int32_t_s_s)(int32_t si1, int32_t si2 )
{
 
  return


    (((si1^si2) & (((si1 ^ ((si1^si2) & (~(2147483647))))-si2)^si2)) < 0) ?
    ((si1)) :


    (si1 - si2);
}

static int32_t
(safe_mul_func_int32_t_s_s)(int32_t si1, int32_t si2 )
{
 
  return


    (((si1 > 0) && (si2 > 0) && (si1 > ((2147483647) / si2))) || ((si1 > 0) && (si2 <= 0) && (si2 < ((-2147483647-1) / si1))) || ((si1 <= 0) && (si2 > 0) && (si1 < ((-2147483647-1) / si2))) || ((si1 <= 0) && (si2 <= 0) && (si1 != 0) && (si2 < ((2147483647) / si1)))) ?
    ((si1)) :


    si1 * si2;
}

static int32_t
(safe_mod_func_int32_t_s_s)(int32_t si1, int32_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-2147483647-1)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 % si2);
}

static int32_t
(safe_div_func_int32_t_s_s)(int32_t si1, int32_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-2147483647-1)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 / si2);
}

static int32_t
(safe_lshift_func_int32_t_s_s)(int32_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > ((2147483647) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static int32_t
(safe_lshift_func_int32_t_s_u)(int32_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32) || (left > ((2147483647) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static int32_t
(safe_rshift_func_int32_t_s_s)(int32_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))?
    ((left)) :

    (left >> ((int)right));
}

static int32_t
(safe_rshift_func_int32_t_s_u)(int32_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32)) ?
    ((left)) :

    (left >> ((unsigned int)right));
}




static int64_t
(safe_unary_minus_func_int64_t_s)(int64_t si )
{
 
  return


    (si==(-9223372036854775807L -1)) ?
    ((si)) :


    -si;
}

static int64_t
(safe_add_func_int64_t_s_s)(int64_t si1, int64_t si2 )
{
 
  return


    (((si1>0) && (si2>0) && (si1 > ((9223372036854775807L)-si2))) || ((si1<0) && (si2<0) && (si1 < ((-9223372036854775807L -1)-si2)))) ?
    ((si1)) :


    (si1 + si2);
}

static int64_t
(safe_sub_func_int64_t_s_s)(int64_t si1, int64_t si2 )
{
 
  return


    (((si1^si2) & (((si1 ^ ((si1^si2) & (~(9223372036854775807L))))-si2)^si2)) < 0) ?
    ((si1)) :


    (si1 - si2);
}

static int64_t
(safe_mul_func_int64_t_s_s)(int64_t si1, int64_t si2 )
{
 
  return


    (((si1 > 0) && (si2 > 0) && (si1 > ((9223372036854775807L) / si2))) || ((si1 > 0) && (si2 <= 0) && (si2 < ((-9223372036854775807L -1) / si1))) || ((si1 <= 0) && (si2 > 0) && (si1 < ((-9223372036854775807L -1) / si2))) || ((si1 <= 0) && (si2 <= 0) && (si1 != 0) && (si2 < ((9223372036854775807L) / si1)))) ?
    ((si1)) :


    si1 * si2;
}

static int64_t
(safe_mod_func_int64_t_s_s)(int64_t si1, int64_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-9223372036854775807L -1)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 % si2);
}

static int64_t
(safe_div_func_int64_t_s_s)(int64_t si1, int64_t si2 )
{
 
  return

    ((si2 == 0) || ((si1 == (-9223372036854775807L -1)) && (si2 == (-1)))) ?
    ((si1)) :

    (si1 / si2);
}

static int64_t
(safe_lshift_func_int64_t_s_s)(int64_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32) || (left > ((9223372036854775807L) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static int64_t
(safe_lshift_func_int64_t_s_u)(int64_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32) || (left > ((9223372036854775807L) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static int64_t
(safe_rshift_func_int64_t_s_s)(int64_t left, int right )
{
 
  return

    ((left < 0) || (((int)right) < 0) || (((int)right) >= 32))?
    ((left)) :

    (left >> ((int)right));
}

static int64_t
(safe_rshift_func_int64_t_s_u)(int64_t left, unsigned int right )
{
 
  return

    ((left < 0) || (((unsigned int)right) >= 32)) ?
    ((left)) :

    (left >> ((unsigned int)right));
}







static uint8_t
(safe_unary_minus_func_uint8_t_u)(uint8_t ui )
{
 
  return -ui;
}

static uint8_t
(safe_add_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 )
{
 
  return ui1 + ui2;
}

static uint8_t
(safe_sub_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 )
{
 
  return ui1 - ui2;
}

static uint8_t
(safe_mul_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 )
{
 
  return ((unsigned int)ui1) * ((unsigned int)ui2);
}

static uint8_t
(safe_mod_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 % ui2);
}

static uint8_t
(safe_div_func_uint8_t_u_u)(uint8_t ui1, uint8_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 / ui2);
}

static uint8_t
(safe_lshift_func_uint8_t_u_s)(uint8_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32) || (left > ((255) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static uint8_t
(safe_lshift_func_uint8_t_u_u)(uint8_t left, unsigned int right )
{
 
  return

    ((((unsigned int)right) >= 32) || (left > ((255) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static uint8_t
(safe_rshift_func_uint8_t_u_s)(uint8_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32)) ?
    ((left)) :

    (left >> ((int)right));
}

static uint8_t
(safe_rshift_func_uint8_t_u_u)(uint8_t left, unsigned int right )
{
 
  return

    (((unsigned int)right) >= 32) ?
    ((left)) :

    (left >> ((unsigned int)right));
}



static uint16_t
(safe_unary_minus_func_uint16_t_u)(uint16_t ui )
{
 
  return -ui;
}

static uint16_t
(safe_add_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 )
{
 
  return ui1 + ui2;
}

static uint16_t
(safe_sub_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 )
{
 
  return ui1 - ui2;
}

static uint16_t
(safe_mul_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 )
{
 
  return ((unsigned int)ui1) * ((unsigned int)ui2);
}

static uint16_t
(safe_mod_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 % ui2);
}

static uint16_t
(safe_div_func_uint16_t_u_u)(uint16_t ui1, uint16_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 / ui2);
}

static uint16_t
(safe_lshift_func_uint16_t_u_s)(uint16_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32) || (left > ((65535) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static uint16_t
(safe_lshift_func_uint16_t_u_u)(uint16_t left, unsigned int right )
{
 
  return

    ((((unsigned int)right) >= 32) || (left > ((65535) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static uint16_t
(safe_rshift_func_uint16_t_u_s)(uint16_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32)) ?
    ((left)) :

    (left >> ((int)right));
}

static uint16_t
(safe_rshift_func_uint16_t_u_u)(uint16_t left, unsigned int right )
{
 
  return

    (((unsigned int)right) >= 32) ?
    ((left)) :

    (left >> ((unsigned int)right));
}



static uint32_t
(safe_unary_minus_func_uint32_t_u)(uint32_t ui )
{
 
  return -ui;
}

static uint32_t
(safe_add_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 )
{
 
  return ui1 + ui2;
}

static uint32_t
(safe_sub_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 )
{
 
  return ui1 - ui2;
}

static uint32_t
(safe_mul_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 )
{
 
  return ((unsigned int)ui1) * ((unsigned int)ui2);
}

static uint32_t
(safe_mod_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 % ui2);
}

static uint32_t
(safe_div_func_uint32_t_u_u)(uint32_t ui1, uint32_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 / ui2);
}

static uint32_t
(safe_lshift_func_uint32_t_u_s)(uint32_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32) || (left > ((4294967295U) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static uint32_t
(safe_lshift_func_uint32_t_u_u)(uint32_t left, unsigned int right )
{
 
  return

    ((((unsigned int)right) >= 32) || (left > ((4294967295U) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static uint32_t
(safe_rshift_func_uint32_t_u_s)(uint32_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32)) ?
    ((left)) :

    (left >> ((int)right));
}

static uint32_t
(safe_rshift_func_uint32_t_u_u)(uint32_t left, unsigned int right )
{
 
  return

    (((unsigned int)right) >= 32) ?
    ((left)) :

    (left >> ((unsigned int)right));
}




static uint64_t
(safe_unary_minus_func_uint64_t_u)(uint64_t ui )
{
 
  return -ui;
}

static uint64_t
(safe_add_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 )
{
 
  return ui1 + ui2;
}

static uint64_t
(safe_sub_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 )
{
 
  return ui1 - ui2;
}

static uint64_t
(safe_mul_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 )
{
 
  return ((unsigned long long int)ui1) * ((unsigned long long int)ui2);
}

static uint64_t
(safe_mod_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 % ui2);
}

static uint64_t
(safe_div_func_uint64_t_u_u)(uint64_t ui1, uint64_t ui2 )
{
 
  return

    (ui2 == 0) ?
    ((ui1)) :

    (ui1 / ui2);
}

static uint64_t
(safe_lshift_func_uint64_t_u_s)(uint64_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32) || (left > ((18446744073709551615UL) >> ((int)right)))) ?
    ((left)) :

    (left << ((int)right));
}

static uint64_t
(safe_lshift_func_uint64_t_u_u)(uint64_t left, unsigned int right )
{
 
  return

    ((((unsigned int)right) >= 32) || (left > ((18446744073709551615UL) >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}

static uint64_t
(safe_rshift_func_uint64_t_u_s)(uint64_t left, int right )
{
 
  return

    ((((int)right) < 0) || (((int)right) >= 32)) ?
    ((left)) :

    (left >> ((int)right));
}

static uint64_t
(safe_rshift_func_uint64_t_u_u)(uint64_t left, unsigned int right )
{
 
  return

    (((unsigned int)right) >= 32) ?
    ((left)) :

    (left >> ((unsigned int)right));
}
# 101 "/home/daniel/s/r_software/csmith-2.1.0/runtime/random_inc.h" 2
# 44 "/home/daniel/s/r_software/csmith-2.1.0/runtime/csmith.h" 2

static uint32_t crc32_tab[256];
static uint32_t crc32_context = 0xFFFFFFFFUL;

static void
crc32_gentab (void)
{
 uint32_t crc;
 const uint32_t poly = 0xEDB88320UL;
 int i, j;

 for (i = 0; i < 256; i++) {
  crc = i;
  for (j = 8; j > 0; j--) {
   if (crc & 1) {
    crc = (crc >> 1) ^ poly;
   } else {
    crc >>= 1;
   }
  }
  crc32_tab[i] = crc;
 }
}

static void
crc32_byte (uint8_t b) {
 crc32_context =
  ((crc32_context >> 8) & 0x00FFFFFF) ^
  crc32_tab[(crc32_context ^ b) & 0xFF];
}
# 94 "/home/daniel/s/r_software/csmith-2.1.0/runtime/csmith.h"
static void
crc32_8bytes (uint64_t val)
{
 crc32_byte ((val>>0) & 0xff);
 crc32_byte ((val>>8) & 0xff);
 crc32_byte ((val>>16) & 0xff);
 crc32_byte ((val>>24) & 0xff);
 crc32_byte ((val>>32) & 0xff);
 crc32_byte ((val>>40) & 0xff);
 crc32_byte ((val>>48) & 0xff);
 crc32_byte ((val>>56) & 0xff);
}

static void
transparent_crc (uint64_t val, char* vname, int flag)
{
 crc32_8bytes(val);
 if (flag) {
    printf("...checksum after hashing %s : %lX\n", vname, crc32_context ^ 0xFFFFFFFFUL);
 }
}
# 11 "main.c" 2


static long __undefined;


#pragma pack(push)
#pragma pack(1)
struct S0 {
   const unsigned f0 : 15;
   signed f1 : 8;
   signed f2 : 10;
   signed f3 : 14;
   const volatile unsigned f4 : 5;
   volatile unsigned f5 : 8;
};
#pragma pack(pop)


static volatile int64_t g_23[3] = {0x14A5EA964A90C6D2LL, 0x14A5EA964A90C6D2LL, 0x14A5EA964A90C6D2LL};
static uint64_t g_24 = 0UL;
static uint64_t g_29[5] = {0x3A4D1B40E11A796DLL, 0x3A4D1B40E11A796DLL, 0x3A4D1B40E11A796DLL, 0x3A4D1B40E11A796DLL, 0x3A4D1B40E11A796DLL};
static uint32_t g_51 = 0xD5B6062CL;
static int32_t g_55[1][9] = {{0x17092FF8L, 0x17092FF8L, 0x17092FF8L, 0x17092FF8L, 0x17092FF8L, 0x17092FF8L, 0x17092FF8L, 0x17092FF8L, 0x17092FF8L}};
static int32_t *g_74[6] = {&g_55[0][2], &g_55[0][2], (void*)0, &g_55[0][2], &g_55[0][2], (void*)0};
static int32_t g_77 = (-2L);
static uint32_t g_98 = 4294967295UL;
static uint32_t g_100[10][2][6] = {{{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}, {{0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}, {0x8EE8584DL, 1UL, 0xBD04657EL, 0xBD04657EL, 1UL, 0x8EE8584DL}}};
static int8_t g_163 = 0L;
static uint8_t g_166 = 3UL;
static volatile uint64_t g_172 = 0xE15430F98853BCE1LL;
static volatile uint64_t *g_171 = &g_172;
static volatile uint64_t **g_170 = &g_171;
static uint32_t g_223 = 0xEC79DE54L;
static uint32_t g_240 = 2UL;
static int8_t g_250 = 0xA8L;
static int64_t g_274 = 0x1B61A870D0B17583LL;
static uint16_t g_327[7] = {0x5F6AL, 0x5F6AL, 0x5F6AL, 0x5F6AL, 0x5F6AL, 0x5F6AL, 0x5F6AL};
static uint16_t g_337 = 0x9ED9L;
static int16_t g_357 = 2L;
static volatile uint8_t g_372[1] = {5UL};
static volatile uint8_t * const g_371 = &g_372[0];
static volatile uint8_t * const volatile *g_370 = &g_371;
static uint64_t g_409 = 0x9AC8733DA6A2FACDLL;
static uint8_t g_410 = 248UL;
static volatile int64_t g_430 = (-1L);
static volatile int64_t *g_429 = &g_430;
static volatile int64_t * const *g_428[4] = {&g_429, &g_429, &g_429, &g_429};
static int64_t *g_443[2][10] = {{&g_274, (void*)0, (void*)0, (void*)0, (void*)0, &g_274, (void*)0, (void*)0, (void*)0, (void*)0}, {&g_274, (void*)0, (void*)0, (void*)0, (void*)0, &g_274, (void*)0, (void*)0, (void*)0, (void*)0}};
static int64_t **g_442 = &g_443[0][1];
static uint32_t * volatile g_505 = &g_98;
static uint32_t * volatile *g_504 = &g_505;
static const int32_t g_525 = 0x3BB9D7D7L;
static int64_t g_544 = 0x0438497B56AECD74LL;
static uint64_t *g_561 = &g_409;
static uint64_t **g_560 = &g_561;
static int32_t *g_589 = &g_55[0][4];
static int32_t g_599 = (-1L);
static volatile uint32_t g_612 = 0xDFE9E5F1L;
static volatile uint32_t *g_611 = &g_612;
static volatile uint32_t **g_610 = &g_611;
static const uint64_t g_632[1] = {0x4A7DDA923595578DLL};
static int64_t * volatile ** volatile g_717 = (void*)0;
static int64_t * volatile ** volatile *g_716[4] = {&g_717, (void*)0, &g_717, (void*)0};
static int64_t ***g_719 = &g_442;
static int64_t ****g_718 = &g_719;
static uint16_t g_762[9] = {65535UL, 65535UL, 0x0D09L, 65535UL, 65535UL, 0x0D09L, 65535UL, 65535UL, 0x0D09L};
static uint32_t *g_817 = &g_240;
static volatile struct S0 g_826 = {110,-11,7,-95,0,9};
static volatile struct S0 g_827 = {71,-7,5,72,3,2};
static volatile struct S0 g_828 = {44,5,-26,32,2,9};
static volatile struct S0 g_829 = {106,8,2,47,0,1};
static volatile struct S0 g_830 = {142,6,15,93,4,7};
static volatile struct S0 g_831 = {18,8,29,-50,3,5};
static volatile struct S0 g_832 = {133,-5,-7,127,2,2};
static volatile struct S0 g_833 = {27,9,9,29,2,1};
static volatile struct S0 *g_825[3][7][1] = {{{&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}}, {{&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}}, {{&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}, {&g_831}}};
static int32_t g_841 = (-5L);
static uint32_t g_858 = 4294967293UL;
static int64_t g_867 = 0x0087666D32D1F71DLL;
static int32_t *g_875 = (void*)0;
static struct S0 g_888 = {152,-12,-18,-1,0,7};
static const uint8_t g_891 = 0x64L;
static struct S0 g_973 = {180,-11,17,-109,0,9};
static int32_t ** volatile g_1030 = &g_74[5];
static struct S0 g_1063 = {158,10,1,-85,0,15};
static uint32_t g_1091 = 0xFC626E05L;
static volatile int64_t g_1095 = 3L;
static int16_t g_1097 = 0x5D77L;
static const int32_t *g_1107 = &g_599;
static const int32_t ** volatile g_1106 = &g_1107;
static volatile struct S0 g_1109 = {42,6,-29,12,2,5};
static int32_t **g_1111 = &g_74[4];
static int32_t *** const volatile g_1110[2] = {&g_1111, &g_1111};
static int32_t *** const volatile g_1113[9][6][4] = {{{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}, {{(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}, {(void*)0, &g_1111, &g_1111, &g_1111}}};
static volatile struct S0 g_1117 = {25,-2,15,-51,3,3};
static int16_t **g_1126 = (void*)0;
static int32_t * volatile g_1128 = &g_55[0][4];
static int32_t * volatile * volatile g_1129[2] = {(void*)0, (void*)0};
static int8_t g_1150 = 6L;
static int64_t g_1171 = (-4L);
static volatile struct S0 g_1195 = {85,-13,20,103,3,7};
static int8_t g_1232 = (-1L);
static int64_t g_1236 = 6L;
static int16_t ***g_1262 = &g_1126;
static volatile struct S0 g_1273 = {122,10,-25,59,4,14};
static const volatile struct S0 g_1323 = {77,10,5,4,4,9};
static const uint64_t g_1340[8] = {18446744073709551615UL, 0x699F91224B88E7D2LL, 18446744073709551615UL, 0x699F91224B88E7D2LL, 18446744073709551615UL, 0x699F91224B88E7D2LL, 18446744073709551615UL, 0x699F91224B88E7D2LL};
static struct S0 *g_1371[5][8][6] = {{{&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}}, {{&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}}, {{&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}}, {{&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}}, {{&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}, {&g_888, &g_1063, &g_973, &g_973, &g_973, &g_1063}}};
static struct S0 ** volatile g_1370 = &g_1371[2][0][0];
static int32_t ** volatile g_1379 = (void*)0;
static const uint32_t g_1399 = 0x05E7DB9EL;
static int16_t g_1477[1][10][7] = {{{0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}, {0L, 0xF930L, 1L, (-10L), 0xAB0BL, 0x21EDL, 0xAB0BL}}};
static int32_t ** volatile g_1494 = &g_589;
static int32_t * volatile g_1511 = &g_55[0][2];
static int32_t g_1528 = 1L;
static int16_t * volatile g_1550 = &g_1477[0][4][1];
static int16_t * volatile *g_1549 = &g_1550;
static int32_t * volatile g_1616[8][10] = {{&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}, {&g_55[0][2], (void*)0, &g_599, &g_77, &g_599, &g_55[0][2], &g_599, &g_77, &g_599, (void*)0}};



static uint64_t func_1(void);
static uint8_t func_10(uint8_t p_11, uint8_t p_12);
static uint16_t func_15(uint32_t p_16, uint32_t p_17, int64_t p_18, uint16_t p_19, uint32_t p_20);
static uint64_t func_25(uint64_t p_26, uint8_t p_27);
static int16_t func_32(uint64_t * p_33);
static uint64_t * func_37(int32_t p_38, uint64_t * p_39);
static const uint16_t func_43(uint8_t p_44, uint64_t * p_45, uint32_t p_46);
static uint64_t * func_47(uint32_t p_48);
static int32_t * func_56(uint32_t * p_57, int64_t p_58, int64_t p_59);
static int16_t func_67(uint32_t * p_68, const uint64_t * p_69, uint32_t p_70, const int32_t p_71);
# 150 "main.c"
static uint64_t func_1(void)
{
    uint8_t l_2 = 0x3AL;
    uint64_t l_5[8] = {18446744073709551612UL, 9UL, 18446744073709551612UL, 9UL, 18446744073709551612UL, 9UL, 18446744073709551612UL, 9UL};
    int32_t l_952 = 0L;
    uint8_t l_954 = 0x62L;
    int64_t l_1525[2];
    uint16_t l_1540 = 0x8C8FL;
    uint64_t **l_1591 = &g_561;
    struct S0 **l_1595 = &g_1371[2][7][3];
    uint32_t *l_1608 = &g_223;
    uint64_t l_1613 = 18446744073709551615UL;
    int i;
    for (i = 0; i < 2; i++)
        l_1525[i] = 0x11C22AD27E21C37FLL;
    l_2--;
    for (l_2 = 0; (l_2 <= 7); l_2 += 1)
    {
        uint64_t *l_28[4][7] = {{&g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1]}, {&g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1]}, {&g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1]}, {&g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1], (void*)0, &g_29[1]}};
        int32_t l_953[5] = {6L, (-5L), 6L, (-5L), 6L};
        uint32_t *l_1535[1][8][4] = {{{&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}, {&g_223, &g_223, (void*)0, &g_223}}};
        int32_t l_1539 = 1L;
        int32_t l_1548[5][1] = {{(-1L)}, {(-1L)}, {(-1L)}, {(-1L)}, {(-1L)}};
        int16_t *l_1552 = &g_1477[0][4][3];
        int16_t **l_1551 = &l_1552;
        uint32_t l_1573 = 2UL;
        int32_t l_1574 = (-1L);
        int64_t l_1575[4] = {1L, 0L, 1L, 0L};
        uint32_t l_1578 = 1UL;
        uint16_t l_1579 = 0x09A4L;
        uint16_t l_1590 = 0xC5F6L;
        int8_t *l_1594 = &g_1150;
        int32_t *l_1609[1][2][9] = {{{&l_1548[3][0], &l_1539, &l_1548[3][0], &l_1539, &l_1548[3][0], &l_1539, &l_1548[3][0], &l_1539, &l_1548[3][0]}, {&l_1548[3][0], &l_1539, &l_1548[3][0], &l_1539, &l_1548[3][0], &l_1539, &l_1548[3][0], &l_1539, &l_1548[3][0]}}};
        int32_t *l_1610 = &l_1574;
        uint32_t *l_1614[1][2];
        int16_t l_1615[2];
        int32_t *l_1617 = &l_953[2];
        int i, j, k;
        for (i = 0; i < 1; i++)
        {
            for (j = 0; j < 2; j++)
                l_1614[i][j] = &g_1091;
        }
        for (i = 0; i < 2; i++)
            l_1615[i] = 0xC1D0L;
    }
    return (*g_171);
}







static uint8_t func_10(uint8_t p_11, uint8_t p_12)
{
    uint32_t *l_1041 = &g_240;
    const uint64_t *l_1042[7] = {&g_632[0], &g_632[0], &g_632[0], &g_632[0], &g_632[0], &g_632[0], &g_632[0]};
    int32_t l_1047 = (-4L);
    uint8_t *l_1048[5];
    uint32_t *l_1050 = &g_100[0][0][1];
    uint32_t **l_1049 = &l_1050;
    const int32_t l_1051 = 0xFCF3A32DL;
    int32_t l_1081 = 3L;
    int32_t l_1096 = (-3L);
    int32_t l_1098 = (-4L);
    uint16_t l_1099 = 0x4F08L;
    int16_t l_1156 = (-7L);
    uint32_t *l_1157 = &g_223;
    uint64_t *l_1237 = &g_24;
    int16_t ***l_1261 = (void*)0;
    struct S0 *l_1300 = &g_888;
    int32_t l_1304 = 0xC13E2C5BL;
    int32_t l_1310[6];
    uint16_t l_1387 = 0x7397L;
    int32_t *l_1409 = &l_1098;
    uint32_t l_1422 = 0xC2A4DA07L;
    uint16_t l_1434 = 0x03A8L;
    uint32_t l_1467 = 4294967294UL;
    int i;
    for (i = 0; i < 5; i++)
        l_1048[i] = &g_166;
    for (i = 0; i < 6; i++)
        l_1310[i] = 0xB953320BL;
    if ((((safe_mul_func_int16_t_s_s(0x02D8L, (safe_div_func_uint32_t_u_u((0x5FAF74CAC4EEFECCLL != p_11), 0x5A7BF675L)))) & (safe_mod_func_uint32_t_u_u((--(**g_504)), func_67(l_1041, l_1042[1], ((g_357 = ((g_410 & (safe_mul_func_int16_t_s_s(((g_867 ^ (safe_div_func_int64_t_s_s((((((((l_1047 = (g_240 || l_1047)) , (void*)0) == (void*)0) && p_11) && 0x7AL) , l_1049) != &l_1050), p_11))) == l_1051), (-1L)))) < 0x5AF3B638189C511ELL)) & g_55[0][6]), l_1051)))) && 0x6AL))
    {
        const int32_t l_1055 = 0L;
        int32_t l_1065 = 0x3E864F9FL;
        int32_t l_1078 = 0x03B7570DL;
        int32_t l_1080 = (-1L);
        int32_t l_1082 = 0x5ED3A2CFL;
        int32_t l_1083 = 0x340914AEL;
        int32_t l_1085 = 0x6D1B040FL;
        int32_t l_1086 = (-2L);
        int32_t l_1088 = (-1L);
        int32_t l_1090 = 0x3FE6D00CL;
        int16_t l_1120 = 1L;
        int32_t * volatile l_1130 = &l_1085;
        uint32_t l_1160 = 0x047247D4L;
        int16_t l_1166 = 0x793AL;
        uint8_t *l_1176 = &g_410;
lbl_1161:
        for (g_223 = 0; (g_223 <= 1); g_223 += 1)
        {
            (*g_589) ^= p_11;
            for (g_240 = 0; (g_240 <= 1); g_240 += 1)
            {
                const int32_t l_1054 = (-4L);
                int i, j;
                (*g_589) |= ((safe_add_func_int8_t_s_s((~0x3CL), l_1054)) || ((*l_1050) = (l_1055 , 0xDAC4A872L)));
            }
        }
        for (g_77 = (-27); (g_77 == 12); g_77++)
        {
            int16_t l_1058 = (-1L);
            struct S0 *l_1062[4][2][8] = {{{&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}, {&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}}, {{&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}, {&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}}, {{&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}, {&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}}, {{&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}, {&g_1063, (void*)0, &g_1063, &g_888, &g_1063, (void*)0, &g_1063, &g_888}}};
            int32_t l_1079 = 0xBE795812L;
            int32_t l_1084 = (-6L);
            int32_t l_1087 = (-7L);
            int32_t l_1089 = (-1L);
            int16_t l_1094 = 0L;
            int i, j, k;
        }
        for (g_163 = 0; (g_163 >= 0); g_163 -= 1)
        {
            int8_t *l_1121 = (void*)0;
            const uint64_t *l_1122[2];
            int32_t *l_1131[3][3][2] = {{{&l_1085, &l_1065}, {&l_1085, &l_1065}, {&l_1085, &l_1065}}, {{&l_1085, &l_1065}, {&l_1085, &l_1065}, {&l_1085, &l_1065}}, {{&l_1085, &l_1065}, {&l_1085, &l_1065}, {&l_1085, &l_1065}}};
            int8_t l_1158 = 0x5FL;
            int i, j, k;
            for (i = 0; i < 2; i++)
                l_1122[i] = &g_632[0];
            for (g_841 = 0; (g_841 >= 0); g_841 -= 1)
            {
                int32_t **l_1108 = &g_74[2];
                int32_t ***l_1112 = (void*)0;
                int32_t ***l_1114 = &g_1111;
                int i;
                (*g_1106) = &l_1051;
                (*l_1108) = &l_1078;
                if (g_372[g_163])
                    break;
                (*l_1114) = (g_1109 , &g_74[5]);
            }
            if (func_67(&g_240, ((((safe_mul_func_int16_t_s_s((-10L), (((g_1117 , &g_372[g_163]) == &p_12) , (safe_mul_func_uint8_t_u_u(l_1120, (l_1078 ^= (4294967295UL == ((*g_589) = (-1L))))))))) <= (p_11 > 0xC6L)) | l_1099) , l_1122[1]), p_11, p_12))
            {
                int16_t *l_1124 = &g_1097;
                int16_t **l_1123 = &l_1124;
                int16_t ***l_1125[6][7] = {{&l_1123, (void*)0, &l_1123, &l_1123, &l_1123, (void*)0, &l_1123}, {&l_1123, (void*)0, &l_1123, &l_1123, &l_1123, (void*)0, &l_1123}, {&l_1123, (void*)0, &l_1123, &l_1123, &l_1123, (void*)0, &l_1123}, {&l_1123, (void*)0, &l_1123, &l_1123, &l_1123, (void*)0, &l_1123}, {&l_1123, (void*)0, &l_1123, &l_1123, &l_1123, (void*)0, &l_1123}, {&l_1123, (void*)0, &l_1123, &l_1123, &l_1123, (void*)0, &l_1123}};
                int32_t l_1127 = 0L;
                int i, j;
                g_1126 = l_1123;
                (*g_589) = (p_12 >= l_1051);
                (*g_589) ^= l_1127;
            }
            else
            {
                l_1130 = g_1128;
                return g_372[g_163];
            }
            (*g_1111) = l_1131[0][1][0];
            for (l_1085 = 1; (l_1085 >= 0); l_1085 -= 1)
            {
                uint16_t *l_1134[4];
                const uint64_t *l_1145 = (void*)0;
                int8_t *l_1148 = &g_250;
                int8_t *l_1149 = &g_1150;
                const int32_t l_1155 = 0x6AB23BE4L;
                int16_t *l_1159[1];
                int i;
                for (i = 0; i < 4; i++)
                    l_1134[i] = &g_337;
                for (i = 0; i < 1; i++)
                    l_1159[i] = (void*)0;
                (*g_589) = (safe_rshift_func_uint16_t_u_u((g_762[7] = p_11), (safe_add_func_uint64_t_u_u((safe_mul_func_uint16_t_u_u((((--p_12) ^ (-6L)) != ((g_357 = ((((safe_mod_func_uint64_t_u_u((safe_lshift_func_uint16_t_u_s((l_1041 != (g_1109.f1 , l_1157)), p_11)), l_1158)) || 246UL) != 0xAB5E69A2F7779CCBLL) & p_11)) >= l_1155)), (-1L))), p_11))));
                (*g_1111) = l_1131[0][1][0];
                if (l_1160)
                    break;
                if (g_223)
                    goto lbl_1161;
            }
        }
        for (p_12 = 0; (p_12 == 35); p_12++)
        {
            uint32_t l_1179 = 9UL;
            if ((((*l_1130) = (safe_add_func_int16_t_s_s(l_1166, 0xB891L))) >= (l_1082 ^= ((safe_lshift_func_int16_t_s_u((safe_rshift_func_int16_t_s_s(g_1171, 14)), 8)) >= (safe_add_func_uint64_t_u_u((0x40A7L <= (((*g_817) = ((l_1051 , l_1176) == (void*)0)) , (!l_1098))), (safe_lshift_func_int8_t_s_u(0x5FL, 6))))))))
            {
                uint32_t l_1180 = 0x00A45F07L;
                l_1180 = (l_1179 |= ((*g_589) ^= ((*l_1130) = (-1L))));
                (*g_589) &= (-1L);
            }
            else
            {
                return (*g_371);
            }
            (*g_589) ^= (safe_div_func_int64_t_s_s((safe_mul_func_int16_t_s_s(p_12, p_12)), (*g_171)));
            if (l_1051)
                break;
        }
    }
    else
    {
        uint64_t *l_1194 = &g_29[4];
        uint8_t l_1196[8][1][7] = {{{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}, {{0xCAL, 0x74L, 0xA8L, 247UL, 1UL, 2UL, 0x37L}}};
        int32_t *l_1197[5];
        uint64_t l_1198 = 0x7943D01FDF12DDB1LL;
        int32_t *l_1210 = (void*)0;
        int32_t *l_1211 = &g_841;
        uint32_t *l_1230[2][7] = {{&g_1091, &g_858, &g_1091, &g_858, &g_1091, &g_858, &g_1091}, {&g_1091, &g_858, &g_1091, &g_858, &g_1091, &g_858, &g_1091}};
        int8_t *l_1231 = &g_1232;
        uint16_t l_1233 = 0x27ABL;
        int64_t *l_1234 = &g_1171;
        int8_t *l_1235[5][1] = {{&g_163}, {&g_163}, {&g_163}, {&g_163}, {&g_163}};
        int16_t l_1249[6] = {0x3A1DL, 0xAAF9L, 0x3A1DL, 0xAAF9L, 0x3A1DL, 0xAAF9L};
        int16_t l_1286 = 0x14CEL;
        struct S0 **l_1298 = (void*)0;
        uint32_t l_1314 = 0x66FC198BL;
        int i, j, k;
        for (i = 0; i < 5; i++)
            l_1197[i] = &g_77;
        l_1198 ^= ((*g_589) = (safe_mul_func_uint16_t_u_u((safe_lshift_func_uint8_t_u_u(253UL, (safe_sub_func_uint32_t_u_u(((*l_1050) ^= (l_1196[5][0][6] = (~(safe_unary_minus_func_uint64_t_u((((((--p_12) && l_1081) > ((1L | p_11) || (**g_170))) != ((*l_1194) = (p_11 , l_1047))) , (((((g_1195 , 0UL) , 2L) ^ p_12) == p_12) , l_1096))))))), p_11)))), 0xE5BDL)));
        for (g_1171 = 2; (g_1171 > 17); g_1171 = safe_add_func_int16_t_s_s(g_1171, 1))
        {
            uint32_t l_1201 = 0x53B9D042L;
            ++l_1201;
        }
        if ((((!(func_43((safe_mul_func_int8_t_s_s((g_1236 = (safe_lshift_func_int16_t_s_u(((((safe_lshift_func_uint8_t_u_s((*g_371), (((((*l_1211) = (-9L)) , ((*l_1234) = (func_32(((*g_560) = &l_1198)) > (5L != ((safe_add_func_uint64_t_u_u((safe_add_func_uint8_t_u_u((((*l_1231) |= ((g_1091 ^= (safe_mod_func_int16_t_s_s(p_12, ((safe_mul_func_uint16_t_u_u((p_12 | (((g_1150 = p_12) <= (safe_div_func_int64_t_s_s(((safe_lshift_func_uint8_t_u_s((safe_add_func_int16_t_s_s((l_1081 <= p_12), g_525)), p_11)) | g_858), l_1099))) || p_12)), g_891)) , g_762[1])))) && p_11)) ^ l_1099), p_12)), l_1233)) != g_1097))))) == l_1051) > 0xF8C381A4L))) >= 0xBCL) > p_12) == 0x4AL), 14))), g_632[0])), l_1237, p_11) , l_1051)) | l_1051) , (-1L)))
        {
            (*g_1111) = func_56(l_1041, ((safe_sub_func_int8_t_s_s(g_888.f4, g_29[0])) , p_11), l_1051);
        }
        else
        {
            uint32_t l_1240 = 4294967292UL;
            int32_t l_1252 = 0x34C102EEL;
            int32_t *l_1270 = (void*)0;
            uint32_t l_1284 = 8UL;
            const uint64_t *l_1285 = (void*)0;
            int32_t l_1309 = 0x90AF406EL;
            int32_t l_1312[9][7][4] = {{{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}, {{(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}, {(-6L), (-2L), 0xC179C3EDL, 0x0E136314L}}};
            int i, j, k;
            if (((*g_589) = func_15(p_11, ((--l_1240) , (func_25(l_1051, l_1240) >= (safe_add_func_uint8_t_u_u((safe_mod_func_int32_t_s_s(0xA4F68D4CL, p_11)), (!((&p_11 != &p_11) | (safe_div_func_uint8_t_u_u((**g_370), p_12)))))))), l_1249[3], g_1171, p_11)))
            {
                l_1047 = (p_11 || 0L);
            }
            else
            {
                l_1252 = p_11;
                (*g_1111) = &l_1081;
                l_1252 = ((*g_589) = 0x31C086DAL);
            }
            for (l_1099 = 0; (l_1099 <= 4); l_1099 += 1)
            {
                uint16_t *l_1263 = &g_762[7];
                int i;
                if (g_327[(l_1099 + 1)])
                    break;
                g_973.f1 ^= (safe_add_func_uint32_t_u_u(g_327[(l_1099 + 2)], (safe_mul_func_uint8_t_u_u((safe_rshift_func_int8_t_s_u((l_1252 = ((void*)0 != l_1197[l_1099])), func_67(((safe_mul_func_uint16_t_u_u(((*l_1263) = (&g_1126 != (g_1262 = l_1261))), ((safe_mod_func_uint8_t_u_u(255UL, (safe_sub_func_int32_t_s_s(0x4071F31DL, (safe_rshift_func_uint8_t_u_s((*g_371), (l_1197[l_1099] != l_1270))))))) >= 7L))) , (void*)0), &g_632[0], p_11, p_12))), 249UL))));
            }
            if ((safe_mul_func_int16_t_s_s(((!(g_1273 , (safe_add_func_uint8_t_u_u((l_1096 = p_11), (l_1099 == l_1047))))) != (safe_lshift_func_int16_t_s_u(((safe_mod_func_uint64_t_u_u(((g_327[1] >= p_11) <= (safe_rshift_func_int16_t_s_s((p_12 ^ (safe_mod_func_uint16_t_u_u(func_67(l_1157, (l_1284 , l_1285), l_1286, p_11), p_12))), 3))), 0x40B74D87A613AAC7LL)) <= 6UL), 0))), p_11)))
            {
                int64_t l_1289 = 0xBCCF44131C55A6A0LL;
                struct S0 ***l_1299 = &l_1298;
                struct S0 **l_1301[3];
                int32_t l_1302 = (-1L);
                int32_t l_1303 = 2L;
                int32_t l_1305 = 9L;
                int32_t l_1306 = (-1L);
                int32_t l_1307 = 0xE28A9DB4L;
                int32_t l_1308 = 0x8AB19C08L;
                int32_t l_1311 = 0xB0EAB5A6L;
                int32_t l_1313[1][7] = {{0x3725104EL, 0x3725104EL, (-1L), 0x3725104EL, 0x3725104EL, (-1L), 0x3725104EL}};
                int i, j;
                for (i = 0; i < 3; i++)
                    l_1301[i] = &l_1300;
                (*g_589) &= (safe_mul_func_int16_t_s_s(l_1289, g_327[4]));
                (*g_589) = ((!(l_1096 ^= (((p_11 != ((((g_829.f4 , p_12) , &l_1197[1]) == &l_1270) > g_100[3][1][1])) <= 65535UL) >= p_12))) != p_11);
                l_1300 = l_1300;
                l_1314++;
            }
            else
            {
                return (**g_370);
            }
            for (l_1047 = 0; (l_1047 == (-15)); --l_1047)
            {
                int8_t l_1319[1][7] = {{1L, 1L, 2L, 1L, 1L, 2L, 1L}};
                int32_t l_1320 = 0x915725BAL;
                int i, j;
                l_1319[0][1] = ((void*)0 == &g_1126);
                l_1320 = l_1156;
                l_1320 = (p_12 && ((((safe_div_func_uint16_t_u_u((((g_1323 , p_12) , 0xB8E1BC14L) | ((safe_mod_func_uint8_t_u_u((l_1319[0][1] & ((((safe_div_func_uint16_t_u_u(p_12, ((p_11 != ((g_1236 != p_11) & g_841)) ^ p_11))) >= p_11) , &g_1126) != &g_1126)), p_12)) , 0x8F4EE119L)), 0x15D9L)) != g_410) , l_1051) & 0xF28AA18EL));
            }
        }
        (*g_589) = l_1098;
    }
    if (p_12)
    {
        uint8_t **l_1333 = &l_1048[2];
        uint8_t ***l_1332 = &l_1333;
        int32_t l_1334 = 0L;
        const uint64_t *l_1347 = &g_632[0];
        uint32_t *l_1357 = &g_223;
        int32_t l_1363 = (-1L);
        (*g_1111) = &l_1310[1];
        for (g_166 = 0; (g_166 <= 1); g_166++)
        {
            const uint64_t *l_1339 = &g_1340[3];
            int16_t l_1348 = 0xCB6DL;
            for (p_12 = 0; (p_12 != 36); ++p_12)
            {
                uint16_t *l_1343 = &g_327[4];
                int32_t *l_1346 = (void*)0;
                l_1334 = ((void*)0 == l_1332);
                (*g_589) = (safe_sub_func_uint32_t_u_u((safe_mul_func_uint8_t_u_u(((0x01942596F52A85A6LL != func_67(&g_223, (l_1339 = &g_29[1]), p_11, (p_11 ^ ((safe_mul_func_uint16_t_u_u(((*l_1343) = p_11), ((p_12 , (safe_sub_func_int16_t_s_s((l_1346 == (l_1081 , (void*)0)), l_1348))) , 1UL))) <= 0x2DL)))) > 7L), l_1334)), p_12));
                if (l_1348)
                    continue;
                if (g_973.f1)
                    goto lbl_1354;
            }
            (*g_589) ^= (safe_rshift_func_uint8_t_u_u(0x35L, (safe_rshift_func_uint16_t_u_u(p_11, 1))));
            (*g_1111) = &l_1334;
            if (l_1310[3])
                continue;
        }
lbl_1354:
        if (((*g_589) ^= p_11))
        {
            for (g_274 = 0; (g_274 >= 0); g_274 -= 1)
            {
                int32_t **l_1353 = &g_589;
                (*l_1353) = ((*g_1111) = &l_1334);
            }
        }
        else
        {
            return l_1334;
        }
        for (g_357 = 0; (g_357 < 21); g_357 = safe_add_func_uint16_t_u_u(g_357, 5))
        {
            uint16_t l_1360[1][10] = {{0x515EL, 0x7A51L, 0UL, 0UL, 0x7A51L, 0x515EL, 0x7A51L, 0UL, 0UL, 0x7A51L}};
            int32_t *l_1364 = (void*)0;
            int i, j;
            (*g_1111) = (func_67(func_56(l_1357, ((safe_sub_func_int32_t_s_s(((*g_589) ^= l_1360[0][4]), (safe_mod_func_uint32_t_u_u((p_12 , l_1363), 0x25E3526BL)))) , l_1334), (l_1096 = (-6L))), l_1237, l_1098, l_1360[0][1]) , &l_1334);
            (*g_1111) = l_1364;
        }
    }
    else
    {
        int32_t *l_1367 = (void*)0;
        int32_t l_1383 = 0x1972D26EL;
        int32_t l_1384 = 0xE0C84B11L;
        int32_t l_1385 = 0x2C081986L;
        int32_t l_1386 = 0L;
        int16_t **l_1391 = (void*)0;
        const int32_t *l_1411[9];
        int32_t l_1413 = (-10L);
        int32_t l_1421[2][8][5];
        int32_t *l_1425 = (void*)0;
        int32_t *l_1426 = &l_1421[1][6][3];
        int32_t *l_1427 = (void*)0;
        int32_t *l_1428[2];
        uint32_t l_1429 = 1UL;
        int i, j, k;
        for (i = 0; i < 9; i++)
            l_1411[i] = &l_1383;
        for (i = 0; i < 2; i++)
        {
            for (j = 0; j < 8; j++)
            {
                for (k = 0; k < 5; k++)
                    l_1421[i][j][k] = 0xED9EAC0BL;
            }
        }
        for (i = 0; i < 2; i++)
            l_1428[i] = &l_1096;
        for (l_1304 = 0; (l_1304 > (-9)); l_1304--)
        {
            return (**g_370);
        }
        (*g_1111) = l_1367;
        if (l_1310[1])
        {
            int16_t l_1377 = 0L;
            int32_t *l_1381 = &l_1047;
            int32_t *l_1382[3][5] = {{&g_77, &g_77, &l_1304, &l_1304, &g_77}, {&g_77, &g_77, &l_1304, &l_1304, &g_77}, {&g_77, &g_77, &l_1304, &l_1304, &g_77}};
            struct S0 **l_1390 = &l_1300;
            int16_t ***l_1392 = &g_1126;
            int i, j;
            for (p_11 = (-8); (p_11 < 1); p_11 = safe_add_func_uint64_t_u_u(p_11, 8))
            {
                uint64_t *l_1372 = &g_29[1];
                int32_t **l_1378 = &g_589;
                int32_t **l_1380 = &l_1367;
                (*g_1370) = l_1300;
                (*l_1380) = ((*l_1378) = ((*g_1111) = func_56(l_1367, (!(g_240 || (safe_add_func_int32_t_s_s((safe_rshift_func_int16_t_s_u(l_1377, 11)), (**g_504))))), l_1310[4])));
                if (l_1377)
                    break;
            }
            --l_1387;
            (*l_1390) = (*g_1370);
            (*l_1392) = l_1391;
        }
        else
        {
            int32_t l_1408[6][8] = {{(-4L), 7L, (-9L), 3L, 0x021737DAL, 0L, 0x4C982D07L, 0x4C969D52L}, {(-4L), 7L, (-9L), 3L, 0x021737DAL, 0L, 0x4C982D07L, 0x4C969D52L}, {(-4L), 7L, (-9L), 3L, 0x021737DAL, 0L, 0x4C982D07L, 0x4C969D52L}, {(-4L), 7L, (-9L), 3L, 0x021737DAL, 0L, 0x4C982D07L, 0x4C969D52L}, {(-4L), 7L, (-9L), 3L, 0x021737DAL, 0L, 0x4C982D07L, 0x4C969D52L}, {(-4L), 7L, (-9L), 3L, 0x021737DAL, 0L, 0x4C982D07L, 0x4C969D52L}};
            const int32_t *l_1410 = &l_1098;
            int32_t l_1414 = 0xCF6B920AL;
            int32_t l_1415[5][6][4] = {{{1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}}, {{1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}}, {{1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}}, {{1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}}, {{1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}, {1L, 0x68DF7590L, 0x2916E67BL, 0L}}};
            int32_t *l_1416 = (void*)0;
            int32_t *l_1417 = (void*)0;
            int32_t *l_1418 = &g_55[0][8];
            int32_t *l_1419 = &l_1383;
            int32_t *l_1420[8] = {&l_1414, &l_1383, &l_1414, &l_1383, &l_1414, &l_1383, &l_1414, &l_1383};
            int i, j, k;
            if ((safe_sub_func_int64_t_s_s((safe_mul_func_uint8_t_u_u((safe_mul_func_uint8_t_u_u((g_1399 | (safe_div_func_uint32_t_u_u((safe_add_func_uint8_t_u_u((safe_rshift_func_int16_t_s_u(((~(p_12 , (safe_add_func_int8_t_s_s((-1L), p_12)))) <= 0x2CL), 10)), l_1408[2][6])), (**g_504)))), l_1304)), 0xFDL)), l_1081)))
            {
                (*g_1111) = l_1409;
                (*g_1128) = ((*g_171) , ((void*)0 == &g_1232));
                l_1411[2] = l_1410;
            }
            else
            {
                const int32_t **l_1412 = &l_1411[8];
                (*l_1412) = l_1410;
            }
            --l_1422;
        }
        l_1429--;
    }
    for (p_11 = 11; (p_11 > 48); p_11 = safe_add_func_int64_t_s_s(p_11, 5))
    {
        int16_t l_1441 = 1L;
        int32_t l_1446 = 9L;
        int64_t **l_1447 = &g_443[0][1];
        int32_t l_1463 = 0L;
        uint16_t l_1464 = 0xDB62L;
        int16_t *l_1470 = &g_357;
        int16_t * const * const l_1482[6] = {&l_1470, &l_1470, &l_1470, &l_1470, &l_1470, &l_1470};
        int32_t *l_1487 = &l_1096;
        int32_t *l_1488 = &l_1096;
        int32_t *l_1489[7];
        int16_t l_1490 = 0x5A34L;
        uint32_t l_1491 = 18446744073709551615UL;
        int i;
        for (i = 0; i < 7; i++)
            l_1489[i] = &l_1463;
        ++l_1434;
        for (l_1098 = 0; (l_1098 <= 8); l_1098 += 1)
        {
            int32_t l_1439[6][3][1] = {{{0x492FF140L}, {0x492FF140L}, {0x492FF140L}}, {{0x492FF140L}, {0x492FF140L}, {0x492FF140L}}, {{0x492FF140L}, {0x492FF140L}, {0x492FF140L}}, {{0x492FF140L}, {0x492FF140L}, {0x492FF140L}}, {{0x492FF140L}, {0x492FF140L}, {0x492FF140L}}, {{0x492FF140L}, {0x492FF140L}, {0x492FF140L}}};
            int16_t *l_1440 = (void*)0;
            uint8_t **l_1453 = &l_1048[3];
            uint8_t ***l_1452 = &l_1453;
            int32_t l_1454 = 0xAE57BDE1L;
            int32_t l_1458 = 0x771F72A6L;
            int32_t l_1459 = 0L;
            int32_t l_1460 = 0x793C6DF9L;
            int16_t l_1461 = 0x96CBL;
            int32_t l_1462[1];
            int16_t l_1483 = 0x35A0L;
            int32_t *l_1484 = &g_77;
            int i, j, k;
            for (i = 0; i < 1; i++)
                l_1462[i] = 0x5118F6BFL;
            if ((safe_sub_func_int16_t_s_s((l_1441 = l_1439[5][1][0]), (safe_mul_func_uint16_t_u_u(0x0399L, (safe_add_func_int8_t_s_s(p_11, (l_1446 < (l_1454 |= ((((l_1447 != ((*g_719) = l_1447)) , ((*l_1409) , (safe_sub_func_int16_t_s_s((safe_rshift_func_int16_t_s_u(p_11, 12)), p_11)))) , (void*)0) != l_1452))))))))))
            {
                int32_t l_1455 = 0xE94FCB46L;
                int32_t *l_1456 = (void*)0;
                int32_t *l_1457[2][2];
                int i, j;
                for (i = 0; i < 2; i++)
                {
                    for (j = 0; j < 2; j++)
                        l_1457[i][j] = &l_1454;
                }
                l_1455 ^= 1L;
                ++l_1464;
            }
            else
            {
                int16_t *l_1471 = &g_357;
                int32_t *l_1472[1][6] = {{&l_1459, &l_1096, &l_1459, &l_1096, &l_1459, &l_1096}};
                int i, j;
                l_1446 = (l_1467 < (l_1304 = (((*l_1471) = (0xAAB1L < (&l_1461 == (l_1470 = &l_1461)))) | 0x9E9FL)));
                if (l_1463)
                    break;
            }
            (*l_1484) ^= ((safe_rshift_func_uint16_t_u_s(p_12, ((((*l_1237) = (0UL ^ (safe_div_func_uint8_t_u_u(((-7L) == (g_1477[0][6][5] = p_12)), (g_410--))))) || ((g_762[l_1098] = (((((**g_370) > p_11) > l_1483) , (*l_1409)) < 1UL)) == l_1439[2][0][0])) , l_1441))) || 0L);
            (*l_1484) = (p_12 || p_11);
        }
        for (p_12 = (-3); (p_12 > 49); p_12++)
        {
            for (g_410 = 0; g_410 < 3; g_410 += 1)
            {
                g_23[g_410] = (-1L);
            }
        }
        ++l_1491;
    }
    (*g_1494) = ((*g_1111) = (void*)0);
    return (*g_371);
}







static uint16_t func_15(uint32_t p_16, uint32_t p_17, int64_t p_18, uint16_t p_19, uint32_t p_20)
{
    uint8_t l_959 = 246UL;
    uint32_t *l_971 = &g_51;
    const uint64_t *l_972 = &g_24;
    uint16_t l_974 = 9UL;
    int32_t l_984 = 0L;
    int32_t l_987 = 0x7B4B93E9L;
    int32_t l_988 = 1L;
    int32_t l_992 = 0L;
    int32_t l_994 = 1L;
    int32_t l_995 = 0x66DDF331L;
    int16_t l_998 = 0x4BADL;
    uint32_t l_999 = 4294967295UL;
    uint64_t *l_1018[1];
    int64_t ** const l_1029 = (void*)0;
    int i;
    for (i = 0; i < 1; i++)
        l_1018[i] = &g_409;
    for (g_166 = 0; (g_166 <= 34); g_166 = safe_add_func_int32_t_s_s(g_166, 1))
    {
        const uint32_t l_966[6] = {1UL, 1UL, 1UL, 1UL, 1UL, 1UL};
        uint8_t *l_968[3];
        uint8_t **l_967 = &l_968[2];
        int32_t l_996 = 0xBB623467L;
        const uint64_t *l_1015 = &g_409;
        int i;
        for (i = 0; i < 3; i++)
            l_968[i] = &g_410;
        ++l_959;
        for (g_337 = 0; (g_337 >= 3); ++g_337)
        {
            uint8_t ***l_969 = &l_967;
            uint64_t *l_970 = &g_29[4];
            const int32_t l_983 = 0L;
            int32_t l_985 = 0xC8C8CD09L;
            int32_t l_993 = 4L;
            int32_t l_997 = 0x8F8265F5L;
            uint32_t *l_1002 = &g_51;
            uint8_t l_1010 = 0x29L;
            if (((*g_589) = ((safe_mod_func_int8_t_s_s(g_833.f2, g_888.f0)) == (((l_966[0] == ((g_762[7] = (((*l_969) = l_967) == (void*)0)) > (p_19 ^ (!l_959)))) || 0xD0DA1A27L) , ((*l_970) = p_18)))))
            {
                return l_959;
            }
            else
            {
                int32_t *l_986[3][9][9] = {{{&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}}, {{&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}}, {{&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}, {&g_77, &l_984, &g_55[0][2], &g_599, &l_985, (void*)0, (void*)0, &l_984, &l_984}}};
                uint8_t l_989 = 0x2BL;
                uint32_t **l_1003[4] = {&l_1002, &l_971, &l_1002, &l_971};
                uint16_t *l_1011 = &g_327[4];
                uint64_t l_1014 = 0x70FEF1EBB3D0DD75LL;
                int i, j, k;
                (*g_589) = func_67(l_971, l_972, (g_973 , l_974), ((0xE419B77DF6E9CFEFLL >= (l_985 = (safe_div_func_uint8_t_u_u((safe_lshift_func_uint8_t_u_u(g_77, ((((((*g_589) = p_17) ^ l_959) != ((safe_div_func_uint32_t_u_u((safe_lshift_func_int16_t_s_u(((l_972 == (void*)0) && g_327[4]), 7)), p_17)) < l_983)) == 0L) < p_20))), l_984)))) , 0xED533885L));
                ++l_989;
                l_999++;
                (*g_589) = (l_996 = (g_841 > ((func_67((l_1002 = l_1002), &g_24, (safe_rshift_func_uint8_t_u_s(((l_984 | l_993) == g_888.f5), ((safe_add_func_uint64_t_u_u((safe_mod_func_int64_t_s_s(0xDEE751740A21142CLL, l_1010)), (((++(*l_1011)) ^ l_1014) >= p_16))) , l_985))), l_985) & p_18) > p_17)));
            }
            l_994 = func_67(&g_223, l_1015, (*g_505), g_525);
        }
        return g_826.f3;
    }
    (*g_589) = (safe_lshift_func_int16_t_s_u(g_372[0], 13));
    (*g_1030) = func_56(l_971, (((**g_504) &= (p_16 | ((safe_sub_func_uint64_t_u_u((((4294967289UL == p_19) >= (-2L)) , p_16), l_995)) || p_20))) == l_974), p_20);
    return p_16;
}







static uint64_t func_25(uint64_t p_26, uint8_t p_27)
{
    uint64_t *l_34 = &g_29[2];
    int16_t *l_760[1];
    int32_t l_761[4] = {0L, 0xC0B2E66AL, 0L, 0xC0B2E66AL};
    int32_t *l_782 = &g_599;
    uint32_t l_864 = 0xBEE2C47FL;
    int32_t l_886[3][3][8] = {{{0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}, {0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}, {0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}}, {{0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}, {0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}, {0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}}, {{0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}, {0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}, {0xAF705073L, 1L, 1L, 0L, 0L, 0L, 1L, 1L}}};
    struct S0 *l_887 = &g_888;
    uint8_t *l_890 = (void*)0;
    uint8_t **l_889 = &l_890;
    uint32_t l_896 = 1UL;
    int64_t l_932 = 0x75EBD1698FDD7DC0LL;
    int i, j, k;
    for (i = 0; i < 1; i++)
        l_760[i] = &g_357;
    if ((0x5AL || ((l_761[3] = func_32(l_34)) & g_762[7])))
    {
        int16_t l_777[9] = {0L, 0xB86AL, 0L, 0xB86AL, 0L, 0xB86AL, 0L, 0xB86AL, 0L};
        const uint32_t *l_778[3][5][6] = {{{(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}}, {{(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}}, {{(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}, {(void*)0, &g_98, &g_100[9][1][4], (void*)0, &g_100[9][1][4], (void*)0}}};
        int32_t l_779 = (-1L);
        int i, j, k;
        for (g_274 = 0; (g_274 != (-21)); g_274 = safe_sub_func_int8_t_s_s(g_274, 4))
        {
            (*g_589) |= 0xCE2F3420L;
        }
        for (g_337 = 0; (g_337 < 43); g_337 = safe_add_func_int8_t_s_s(g_337, 1))
        {
            uint32_t *l_767 = &g_51;
            int32_t l_770 = 1L;
            int32_t *l_780 = &g_77;
            int32_t **l_781[10] = {&g_74[5], &g_74[5], &g_74[5], &g_74[5], &g_74[5], &g_74[5], &g_74[5], &g_74[5], &g_74[5], &g_74[5]};
            int i;
            (*l_780) |= (func_67(l_767, &p_26, l_761[2], (l_779 &= (((((*g_589) = (l_770 ^ (*g_589))) < (((safe_sub_func_uint8_t_u_u(p_26, (safe_sub_func_uint8_t_u_u((((((((safe_sub_func_int16_t_s_s(l_777[5], g_51)) != (65530UL <= g_29[1])) != 0xF09E1ADC9B03CB70LL) , p_26) , 0xF643L) & p_26) == 0x09E89397L), l_761[2])))) , (void*)0) == l_778[1][1][2])) , g_762[7]) >= g_544))) < 0L);
            l_782 = &g_77;
        }
    }
    else
    {
        uint64_t l_787 = 1UL;
        int32_t l_789 = (-7L);
        uint32_t l_811 = 0xBB51CC67L;
        uint32_t *l_816 = &g_240;
        uint8_t *l_820 = &g_166;
        uint8_t **l_819 = &l_820;
        int32_t *l_854[6];
        int i;
        for (i = 0; i < 6; i++)
            l_854[i] = (void*)0;
        for (g_599 = 23; (g_599 > (-24)); g_599 = safe_sub_func_int32_t_s_s(g_599, 2))
        {
            uint32_t *l_788 = (void*)0;
            const int32_t l_801[5] = {1L, 1L, 1L, 1L, 1L};
            int32_t l_802 = 6L;
            const uint16_t l_803 = 65534UL;
            int i;
            (*g_589) = p_26;
            if ((safe_lshift_func_int8_t_s_s((l_787 > (l_787 || func_43(g_51, &l_787, ((l_789 = p_26) && ((safe_unary_minus_func_uint8_t_u((((safe_sub_func_uint16_t_u_u(p_27, (safe_sub_func_int16_t_s_s((safe_sub_func_int64_t_s_s((+(l_802 |= (0xEFL == (safe_div_func_int8_t_s_s(func_67(func_56(l_788, (safe_mod_func_int64_t_s_s(p_27, 0x081ACEF0BA07E0DALL)), p_27), (*g_560), g_357, l_801[2]), 0x6DL))))), p_27)), p_26)))) , p_27) != 0x10L))) >= l_803))))), 4)))
            {
                int32_t *l_804 = &l_789;
                int32_t *l_805 = &l_761[1];
                int32_t *l_806 = &l_789;
                int32_t *l_807 = &g_55[0][2];
                int32_t *l_808 = (void*)0;
                int32_t *l_809 = (void*)0;
                int32_t *l_810 = (void*)0;
                --l_811;
                (*l_805) ^= (*g_589);
                (*g_589) = p_26;
                if ((*l_782))
                    continue;
            }
            else
            {
                uint32_t *l_818 = &g_240;
                const uint64_t *l_821 = &g_632[0];
                int8_t *l_822 = (void*)0;
                int8_t *l_823[1];
                int i;
                for (i = 0; i < 1; i++)
                    l_823[i] = &g_250;
                (*g_589) = ((safe_add_func_uint32_t_u_u(((p_27 , func_67(func_56((g_817 = l_816), p_27, (((func_67(l_818, (*g_560), (0xB9L ^ g_51), ((l_819 == &g_371) && g_29[1])) < (-1L)) & p_26) , 0xDA51FB91F337257FLL)), l_821, p_26, g_337)) , p_26), 0x536798C6L)) <= l_802);
                l_789 = (p_27 && (g_163 = p_26));
            }
            for (g_250 = 0; (g_250 <= 3); g_250 += 1)
            {
                const uint32_t l_824 = 5UL;
                volatile struct S0 **l_834 = &g_825[1][6][0];
                uint32_t *l_835 = &g_51;
                int32_t *l_839 = (void*)0;
                int32_t *l_840 = &g_841;
                int32_t *l_842 = (void*)0;
                int32_t *l_843[2][1];
                int i, j;
                for (i = 0; i < 2; i++)
                {
                    for (j = 0; j < 1; j++)
                        l_843[i][j] = &l_761[3];
                }
                if (l_824)
                    break;
                (*l_834) = g_825[0][6][0];
                g_77 ^= (func_67((l_824 , l_835), &p_26, ((*l_782) <= (l_802 , ((p_27 , &g_250) != (void*)0))), ((*l_840) = (safe_unary_minus_func_uint32_t_u(func_67(((safe_mul_func_uint8_t_u_u(l_811, 0x9EL)) , (void*)0), (*g_560), g_599, l_802))))) || 1UL);
                l_802 ^= p_27;
            }
        }
        l_761[3] ^= (safe_sub_func_uint8_t_u_u((((void*)0 != &g_589) , (safe_sub_func_int16_t_s_s((safe_div_func_uint32_t_u_u((safe_div_func_uint64_t_u_u((((safe_sub_func_uint16_t_u_u(65535UL, (func_67(l_816, &l_787, l_789, func_67((((p_27 == (p_26 , (g_632[0] >= g_544))) != p_26) , l_816), &l_787, g_223, g_100[9][1][4])) == 7L))) & (*l_782)) , 6UL), p_27)), (*l_782))), 1L))), p_27));
        if (p_27)
        {
            uint32_t l_855 = 1UL;
            int32_t l_856 = 0L;
            int32_t l_857[5];
            uint16_t l_865 = 0xA7E0L;
            int i;
            for (i = 0; i < 5; i++)
                l_857[i] = 0xA18ECE49L;
            l_856 = l_855;
            --g_858;
            for (l_855 = 0; (l_855 < 48); ++l_855)
            {
                int64_t l_863 = 0xDE42EE938FCD26B9LL;
                int64_t *l_866 = &g_867;
                int32_t **l_868 = (void*)0;
                int32_t **l_869 = &g_74[5];
                if (l_863)
                    break;
                (*l_869) = func_56(&g_223, (func_32(&l_787) ^ ((~((+l_855) || g_858)) != l_863)), ((*l_866) = (l_864 && (0x9C8CB1DFL != (p_26 && l_865)))));
            }
            return l_865;
        }
        else
        {
            uint16_t l_872 = 0x9E59L;
            for (g_410 = 0; (g_410 <= 5); g_410 += 1)
            {
                (*g_589) &= ((*l_782) ^= (safe_div_func_uint16_t_u_u((p_27 ^ (0L >= g_327[2])), l_872)));
            }
            (*g_589) |= p_27;
            return (*g_561);
        }
    }
    l_886[1][2][7] &= ((((((p_26 == (((((((**g_560) && func_32(((*g_560) = &p_26))) , (((*l_782) = (safe_add_func_uint64_t_u_u((*l_782), ((g_875 = l_782) != l_782)))) < ((safe_div_func_uint64_t_u_u((((safe_add_func_uint8_t_u_u((safe_div_func_int8_t_s_s((((safe_add_func_int16_t_s_s(((safe_div_func_int8_t_s_s(((((p_27 |= p_26) , (*g_610)) == l_782) == g_274), 0x3BL)) , l_761[3]), p_26)) , 0x081B0C48E79E0901LL) >= (**g_560)), g_98)), l_864)) && (*g_561)) , (*g_561)), p_26)) , g_327[4]))) != p_26) , (*l_782)) < p_26) , (*l_782))) && (*l_782)) ^ 8L) != p_26) , p_26) , 0L);
    if ((((0xF46FCA66L | 0x3940474CL) , (((((*l_782) , l_887) != l_887) && ((*l_782) == (func_67(l_782, (*g_560), func_67(((((l_889 == (void*)0) & p_26) , (*g_817)) , l_782), (*g_560), (*l_782), p_27), (*l_782)) || (*l_782)))) , (*l_782))) <= g_891))
    {
        (*l_782) = p_26;
    }
    else
    {
        uint16_t l_908 = 0UL;
        int32_t *l_924[6][2][3] = {{{(void*)0, &g_55[0][8], &g_77}, {(void*)0, &g_55[0][8], &g_77}}, {{(void*)0, &g_55[0][8], &g_77}, {(void*)0, &g_55[0][8], &g_77}}, {{(void*)0, &g_55[0][8], &g_77}, {(void*)0, &g_55[0][8], &g_77}}, {{(void*)0, &g_55[0][8], &g_77}, {(void*)0, &g_55[0][8], &g_77}}, {{(void*)0, &g_55[0][8], &g_77}, {(void*)0, &g_55[0][8], &g_77}}, {{(void*)0, &g_55[0][8], &g_77}, {(void*)0, &g_55[0][8], &g_77}}};
        int i, j, k;
        if ((*l_782))
        {
            int32_t *l_892 = &g_55[0][2];
            int32_t *l_893 = (void*)0;
            int32_t *l_894 = &g_55[0][6];
            int32_t *l_895[10][5] = {{(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}, {(void*)0, &l_886[0][1][6], (void*)0, &l_886[1][2][7], &g_55[0][2]}};
            int i, j;
            l_896--;
        }
        else
        {
            int32_t *l_899 = &l_886[1][2][7];
            int32_t *l_900 = &g_599;
            int32_t *l_901 = &l_761[3];
            int32_t *l_902 = &g_55[0][0];
            int32_t *l_903 = &l_761[0];
            int32_t *l_904 = (void*)0;
            int32_t *l_905 = &g_55[0][2];
            int32_t *l_906 = &g_55[0][7];
            int32_t *l_907[1];
            int8_t *l_913[3][6] = {{&g_163, &g_163, &g_250, &g_250, &g_250, &g_250}, {&g_163, &g_163, &g_250, &g_250, &g_250, &g_250}, {&g_163, &g_163, &g_250, &g_250, &g_250, &g_250}};
            int64_t * const l_916[8][6][3] = {{{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}, {{&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}, {&g_274, (void*)0, &g_544}}};
            uint64_t **l_919 = &l_34;
            int32_t l_936 = 0xB23CE4F9L;
            int8_t l_951 = (-6L);
            int i, j, k;
            for (i = 0; i < 1; i++)
                l_907[i] = &g_55[0][3];
            --l_908;
            if (((p_26 < (p_26 , ((safe_lshift_func_int8_t_s_u(((*l_899) = 1L), 1)) && (safe_add_func_int32_t_s_s(1L, (((!(*g_875)) , (p_26 ^ func_32(((*l_919) = func_37((l_916[6][4][2] != ((l_908 >= (safe_sub_func_int8_t_s_s((((g_100[9][1][4] < p_26) != p_27) <= g_525), p_26))) , l_916[7][2][2])), l_34))))) || 0x3AL)))))) ^ l_908))
            {
                uint32_t *l_920[5][1] = {{&g_240}, {&g_240}, {&g_240}, {&g_240}, {&g_240}};
                int32_t l_921 = 0x83813255L;
                int32_t **l_922 = (void*)0;
                int32_t **l_923 = &l_782;
                int i, j;
                (*l_923) = func_56(l_920[0][0], l_921, p_27);
                l_924[2][0][0] = (void*)0;
            }
            else
            {
                uint64_t l_931 = 0xF90BF6D30024C3FELL;
                uint32_t **l_933[4][5] = {{&g_817, &g_817, &g_817, &g_817, &g_817}, {&g_817, &g_817, &g_817, &g_817, &g_817}, {&g_817, &g_817, &g_817, &g_817, &g_817}, {&g_817, &g_817, &g_817, &g_817, &g_817}};
                const uint64_t *l_935 = &g_632[0];
                const uint64_t **l_934 = &l_935;
                int64_t l_937[3][7][10] = {{{0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}}, {{0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}}, {{0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}, {0x664A8B289D3C71BDLL, 0x2AD6DD0F80D972ACLL, 0x04BEAB4FEB7D9A17LL, 0xE3810CC44BBA0A24LL, 0xE7FA00491B04AE25LL, 0x8F020CC8228DBC68LL, 0x478EB03E02DD1EA3LL, 0x478EB03E02DD1EA3LL, 0x8F020CC8228DBC68LL, 0xE7FA00491B04AE25LL}}};
                uint8_t *l_938 = &g_410;
                int32_t l_939 = 0x5879FC46L;
                uint32_t *l_942 = (void*)0;
                int i, j, k;
                l_939 ^= ((((((*l_938) = ((~(safe_add_func_uint64_t_u_u(((**l_919) = 18446744073709551608UL), (safe_div_func_int64_t_s_s((g_762[4] || ((safe_mod_func_int32_t_s_s(((l_931 > (l_932 > l_937[2][1][4])) || (*l_906)), (*l_782))) <= g_858)), 0x2073FB0FD4C2FBAALL))))) < (*l_782))) , l_931) < 4UL) , &g_370) != &g_370);
                (*g_589) ^= (safe_add_func_uint32_t_u_u(((*l_782) = 0x6758A13EL), (safe_mod_func_int8_t_s_s((safe_div_func_int16_t_s_s(9L, g_327[5])), (safe_div_func_int32_t_s_s((safe_mul_func_int16_t_s_s((l_951 = p_27), p_26)), p_27))))));
            }
        }
    }
    return l_896;
}







static int16_t func_32(uint64_t * p_33)
{
    uint32_t l_40 = 9UL;
    uint8_t l_49 = 0x7EL;
    uint32_t *l_50[2];
    int32_t l_52 = 9L;
    uint64_t *l_408 = &g_409;
    uint64_t **l_653 = &g_561;
    int16_t l_654[2][8][3] = {{{(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}}, {{(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}, {(-8L), 0L, 1L}}};
    int32_t l_672 = 4L;
    int32_t l_673 = (-8L);
    int32_t l_674 = 0xE6BA576DL;
    int32_t l_676 = (-1L);
    int32_t l_679 = 0x5F5E4D82L;
    int32_t l_681 = 5L;
    int32_t l_682 = 0x1D01A443L;
    uint32_t l_683 = 1UL;
    int64_t **l_703 = &g_443[0][1];
    uint8_t **l_710 = (void*)0;
    uint8_t ***l_709 = &l_710;
    const uint32_t l_715 = 18446744073709551607UL;
    uint16_t l_749 = 0UL;
    int32_t l_752 = 0xFDD9FED1L;
    int32_t l_753[3][10][8] = {{{0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}}, {{0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}}, {{0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}, {0x56AC68CEL, 0xD58DAC71L, (-2L), 0x8D9BF63BL, (-1L), (-1L), 1L, 0xA71D2A08L}}};
    int i, j, k;
    for (i = 0; i < 2; i++)
        l_50[i] = &g_51;
    if ((safe_sub_func_uint64_t_u_u(((*l_408) = (l_654[0][4][2] = (&g_24 != ((((*l_653) = func_37((l_40 > (l_40 ^ ((safe_rshift_func_uint16_t_u_u(func_43((g_24 , 1UL), func_47((l_52 = (g_51 = l_49))), (g_410 ^= (((safe_add_func_int32_t_s_s(g_250, (((*l_408) &= l_40) > l_49))) ^ l_49) == 0L))), l_40)) > l_40))), &g_24)) != (*g_170)) , (void*)0)))), l_40)))
    {
        const int32_t *l_656 = &g_55[0][7];
        const int32_t **l_657 = &l_656;
        for (g_250 = 0; (g_250 <= 3); g_250 += 1)
        {
            uint32_t l_655 = 0xD93CCCFEL;
            return l_655;
        }
        if (g_166)
            goto lbl_658;
lbl_658:
        (*l_657) = l_656;
        for (g_166 = 0; g_166 < 6; g_166 += 1)
        {
            g_74[g_166] = (void*)0;
        }
    }
    else
    {
        int8_t l_671 = (-2L);
        int32_t l_675[3];
        int32_t *l_686 = &g_599;
        const uint8_t **l_726 = (void*)0;
        uint64_t *l_737 = &g_29[1];
        const int64_t *** const * const *l_738 = (void*)0;
        int64_t *l_739[8][4][2] = {{{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}, {{&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}, {&g_274, &g_544}}};
        int32_t *l_742 = &l_673;
        int i, j, k;
        for (i = 0; i < 3; i++)
            l_675[i] = 0x16D0D3EAL;
        for (g_337 = (-17); (g_337 != 43); g_337 = safe_add_func_uint64_t_u_u(g_337, 1))
        {
            int32_t * const l_666 = &g_55[0][2];
            int32_t *l_667[8];
            int i;
            for (i = 0; i < 8; i++)
                l_667[i] = &g_55[0][5];
            for (g_166 = (-12); (g_166 > 23); g_166 = safe_add_func_uint8_t_u_u(g_166, 4))
            {
                int64_t ***l_664 = &g_442;
                int64_t ****l_663 = &l_664;
                int64_t *****l_665 = (void*)0;
                (*g_589) = ((l_663 = l_663) != (void*)0);
                l_667[2] = l_666;
            }
            for (g_166 = 0; (g_166 >= 2); ++g_166)
            {
                int32_t l_670 = 0x9BFB9D83L;
                int32_t l_677 = (-9L);
                int32_t l_678 = (-10L);
                int32_t l_680[4][9][6] = {{{0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}}, {{0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}}, {{0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}}, {{0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}, {0x6A485179L, 0L, 1L, 0xFD04B666L, (-5L), (-1L)}}};
                int i, j, k;
                l_683--;
            }
            l_686 = l_666;
        }
        for (g_223 = 0; (g_223 >= 58); ++g_223)
        {
            int32_t *l_689 = (void*)0;
            int32_t *l_690 = &l_675[0];
            int32_t *l_691 = &l_682;
            int32_t *l_692 = &l_674;
            int32_t *l_693 = &g_77;
            int32_t *l_694[2][5][5] = {{{&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}}, {{&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}, {&l_675[0], &l_52, &l_675[0], &g_55[0][4], (void*)0}}};
            uint32_t l_695 = 0xC32329CEL;
            int i, j, k;
            --l_695;
            for (g_250 = 0; (g_250 == 6); g_250 = safe_add_func_uint32_t_u_u(g_250, 6))
            {
                uint32_t *l_700 = &g_223;
                const int64_t *l_705 = (void*)0;
                const int64_t **l_704 = &l_705;
                int32_t l_706 = 2L;
                int16_t *l_707[7] = {&l_654[0][5][0], &l_654[0][4][2], &l_654[0][5][0], &l_654[0][4][2], &l_654[0][5][0], &l_654[0][4][2], &l_654[0][5][0]};
                int32_t **l_708 = &l_689;
                int64_t *****l_720 = &g_718;
                int i;
                (*l_708) = func_56(l_700, (8L <= 18446744073709551612UL), ((+((*l_686) = (func_67(&g_223, ((*l_686) , (void*)0), ((((void*)0 == &l_683) == (l_703 != l_704)) , 0x33DC7F70L), l_49) | l_706))) == g_100[9][1][4]));
                (*l_708) = func_56(&l_40, (l_709 == &g_370), (safe_sub_func_uint64_t_u_u(func_67(((0x267928430A39AEFELL && ((**l_708) && (safe_lshift_func_uint8_t_u_u((**l_708), (((*l_686) & 0xFFL) && func_67((((*l_693) , (*l_686)) , (void*)0), (*g_560), g_240, g_240)))))) , &l_40), (*g_560), (**l_708), l_715), 6UL)));
                (*g_589) |= (g_716[2] == ((*l_720) = g_718));
                (*l_690) &= (safe_unary_minus_func_int8_t_s(((safe_lshift_func_uint16_t_u_u(g_98, 7)) & ((**l_708) <= l_49))));
            }
        }
        l_673 = (safe_add_func_int8_t_s_s(((l_726 == (l_40 , l_726)) <= (safe_mod_func_uint64_t_u_u((((((safe_lshift_func_uint8_t_u_u(((safe_mod_func_int8_t_s_s((((*l_686) = ((((safe_div_func_uint32_t_u_u((((func_67(func_56(l_686, (((safe_sub_func_uint64_t_u_u((func_43(g_51, l_737, (((((l_738 == &g_716[2]) , ((*l_686) , (-9L))) && (*p_33)) , (*l_686)) == 9L)) | g_632[0]), l_679)) ^ g_327[5]) >= 0x1F7106ECL), l_675[0]), p_33, l_49, g_544) != l_683) >= g_327[4]) ^ l_40), 4294967294UL)) | g_599) , 18446744073709551608UL) != l_673)) > l_671), l_49)) , l_673), l_715)) , 0UL) == 0xF9F3L) && (*l_686)) >= 0xD9C1214AL), l_674))), l_674));
        if ((((*l_742) &= func_43(l_52, p_33, (safe_lshift_func_uint16_t_u_u(0x0BF6L, (*l_686))))) | (safe_mul_func_uint16_t_u_u(g_409, l_49))))
        {
            int16_t l_747 = 0x7F29L;
            int64_t *l_748 = (void*)0;
            int32_t *l_750[7][1] = {{&l_674}, {&l_674}, {&l_674}, {&l_674}, {&l_674}, {&l_674}, {&l_674}};
            int32_t l_751 = 0x56F40804L;
            uint32_t l_754 = 0x0C146823L;
            int i, j;
            if (((*l_742) , (safe_lshift_func_uint16_t_u_u((*l_686), 15))))
            {
                (*l_686) = (+l_747);
            }
            else
            {
                l_749 = ((void*)0 != l_748);
            }
            --l_754;
            l_753[1][5][0] |= ((*l_742) = (((l_679 == (*l_742)) > (*l_742)) >= ((((0xBAA60372L && 0x1B114056L) && ((*l_686) = ((void*)0 != &l_50[1]))) ^ ((safe_mod_func_uint8_t_u_u((*l_742), g_327[4])) != (*l_742))) >= g_274)));
        }
        else
        {
            int32_t *l_759 = &l_681;
            (*l_686) ^= 0x2E5724B6L;
            l_759 = func_56(l_686, l_654[0][4][2], l_681);
        }
    }
    return l_683;
}







static uint64_t * func_37(int32_t p_38, uint64_t * p_39)
{
    uint32_t *l_628 = &g_223;
    const uint64_t **l_629 = (void*)0;
    const uint64_t *l_631 = &g_632[0];
    const uint64_t **l_630 = &l_631;
    uint32_t *l_637 = &g_51;
    uint32_t **l_636 = &l_637;
    int32_t l_644 = 8L;
    uint8_t *l_645 = (void*)0;
    int32_t l_646 = 2L;
    uint8_t *l_647 = &g_166;
    uint8_t l_650 = 0xDDL;
    int8_t l_651 = 0x95L;
    int32_t l_652[6][7] = {{0xB5D414FCL, 0x294452B3L, 0L, 0xD2422313L, 0x56C4A0DEL, 0xD2422313L, 0L}, {0xB5D414FCL, 0x294452B3L, 0L, 0xD2422313L, 0x56C4A0DEL, 0xD2422313L, 0L}, {0xB5D414FCL, 0x294452B3L, 0L, 0xD2422313L, 0x56C4A0DEL, 0xD2422313L, 0L}, {0xB5D414FCL, 0x294452B3L, 0L, 0xD2422313L, 0x56C4A0DEL, 0xD2422313L, 0L}, {0xB5D414FCL, 0x294452B3L, 0L, 0xD2422313L, 0x56C4A0DEL, 0xD2422313L, 0L}, {0xB5D414FCL, 0x294452B3L, 0L, 0xD2422313L, 0x56C4A0DEL, 0xD2422313L, 0L}};
    int i, j;
    l_652[1][4] |= ((safe_lshift_func_uint16_t_u_u((func_67(l_628, ((*l_630) = p_39), ((safe_add_func_int8_t_s_s((safe_unary_minus_func_uint32_t_u((func_67(((*l_636) = (void*)0), func_47((((safe_mul_func_int16_t_s_s((g_337 && (safe_add_func_uint16_t_u_u((((safe_mul_func_uint8_t_u_u(((*l_647)--), l_646)) , (func_43((g_410 = (func_67(&g_51, p_39, ((g_525 , p_38) == 0xA029D21AL), p_38) > p_38)), p_39, g_77) >= 0xF62BL)) | g_632[0]), 4UL))), p_38)) || l_644) , 0x4118782DL)), l_650, l_646) , l_646))), l_646)) >= 65535UL), p_38) , l_646), 7)) != l_651);
    return (*g_560);
}







static const uint16_t func_43(uint8_t p_44, uint64_t * p_45, uint32_t p_46)
{
    int32_t l_431 = (-1L);
    uint64_t *l_433 = &g_29[1];
    uint64_t **l_432 = &l_433;
    int64_t **l_445 = (void*)0;
    int32_t **l_454 = (void*)0;
    uint16_t l_471 = 0x596FL;
    uint32_t *l_472 = &g_223;
    const int16_t l_533 = 1L;
    const int8_t l_536[10][5] = {{0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}, {0x87L, 0x87L, 0L, 0x02L, 0x32L}};
    int32_t l_582[7][7] = {{(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}, {(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}, {(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}, {(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}, {(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}, {(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}, {(-10L), (-6L), (-10L), 0x50282AEAL, 0xAEAE5535L, 6L, 0xF54A651DL}};
    int32_t *l_591 = &g_55[0][2];
    int32_t l_592 = 2L;
    int32_t l_593[2][10][8] = {{{1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}}, {{1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}, {1L, 6L, 0x6C69667AL, 6L, 1L, 1L, 0x6C69667AL, 1L}}};
    int16_t l_595 = 3L;
    int32_t *l_622 = &g_55[0][5];
    int i, j, k;
    for (g_274 = (-8); (g_274 >= 21); g_274++)
    {
        uint64_t l_413[10][3][3] = {{{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}, {{0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}, {0x8D4B4F2838D5244CLL, 18446744073709551611UL, 0x18CC3C2349389C57LL}}};
        int8_t *l_414 = &g_163;
        uint8_t *l_423 = &g_410;
        uint64_t ** const l_434 = &l_433;
        int16_t *l_435 = &g_357;
        uint32_t *l_441 = &g_100[9][1][4];
        int64_t ***l_469 = &g_442;
        uint16_t l_491 = 1UL;
        uint16_t l_506[4] = {3UL, 0x9A02L, 3UL, 0x9A02L};
        int32_t l_545 = 0xAEB4896CL;
        int32_t l_546 = 0L;
        int i, j, k;
        if ((((g_100[4][1][4] , ((*l_414) = l_413[6][2][2])) , ((*l_435) = ((((((l_413[6][2][2] < ((((*l_423) ^= (safe_rshift_func_int16_t_s_s((safe_mod_func_uint8_t_u_u((252UL == (safe_add_func_int64_t_s_s(0L, 0xEB6F0B40B7054F3DLL))), 1L)), 1))) , g_163) >= (safe_div_func_uint8_t_u_u(((((safe_mod_func_int8_t_s_s(0xFEL, 0x3CL)) , g_428[1]) == (void*)0) && l_431), p_46)))) , l_432) != l_434) | p_46) , g_98) != l_431))) , l_413[6][2][2]))
        {
            uint16_t l_453[4][5][6] = {{{8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}}, {{8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}}, {{8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}}, {{8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}, {8UL, 0xD699L, 0x0DCEL, 6UL, 0x1EECL, 1UL}}};
            int i, j, k;
            for (g_51 = 0; (g_51 == 22); g_51++)
            {
                uint32_t *l_438 = &g_51;
                int64_t ***l_444[3];
                const int32_t l_448[2] = {0xCB86FA16L, 0xCB86FA16L};
                int32_t **l_455 = (void*)0;
                int32_t **l_456 = &g_74[0];
                int32_t *l_458 = (void*)0;
                int32_t **l_457 = &l_458;
                int32_t *l_459 = &l_431;
                int i;
                for (i = 0; i < 3; i++)
                    l_444[i] = &g_442;
                (*l_457) = ((*l_456) = func_56(l_438, (((((&g_100[1][0][3] != l_441) , &g_429) != (l_445 = g_442)) >= ((safe_sub_func_uint32_t_u_u(l_448[0], (safe_sub_func_uint32_t_u_u((~(((safe_mul_func_uint8_t_u_u(p_46, l_453[0][1][3])) , l_454) == &g_74[5])), p_46)))) <= l_448[0])) , 0x52D2D01060767E86LL), l_448[0]));
                (*l_459) |= 0L;
            }
            if (p_44)
            {
                int32_t *l_460 = &g_77;
                (*l_460) = 0x085F9AEFL;
                return p_46;
            }
            else
            {
                uint32_t l_461 = 1UL;
                int32_t *l_462 = (void*)0;
                int32_t *l_463 = &l_431;
                (*l_463) = l_461;
            }
        }
        else
        {
            uint32_t *l_464 = (void*)0;
            int64_t ****l_470 = &l_469;
            int32_t l_473 = 0x4E88B2DAL;
            const uint8_t l_474[2] = {0xF9L, 0xF9L};
            uint32_t *l_475 = &g_98;
            const uint64_t *l_490 = (void*)0;
            int i;
            if ((~func_67(l_464, &g_409, ((*l_475) &= ((*l_441) &= ((g_163 & (safe_div_func_int8_t_s_s(((l_473 = (((0L ^ ((((*l_472) = func_67(&g_51, p_45, (func_67(((safe_mul_func_uint8_t_u_u((((*l_470) = l_469) == &g_428[1]), (p_46 & l_471))) , l_472), &g_409, l_473, l_474[0]) == p_46), p_46)) , p_44) != 0xCEAB1A1746ABD2DCLL)) , p_46) ^ g_410)) != g_77), p_46))) != 0xA41FL))), p_46)))
            {
                int32_t **l_476 = &g_74[5];
                int32_t l_477 = (-1L);
                (*l_476) = &g_55[0][7];
                if (l_477)
                    break;
            }
            else
            {
                uint32_t *l_482 = (void*)0;
                int32_t l_489 = 0L;
                int32_t *l_492[1][2];
                int16_t l_493[8] = {0x9795L, 0x9795L, 0x3FEDL, 0x9795L, 0x9795L, 0x3FEDL, 0x9795L, 0x9795L};
                int i, j;
                for (i = 0; i < 1; i++)
                {
                    for (j = 0; j < 2; j++)
                        l_492[i][j] = &l_431;
                }
                l_493[3] |= (l_473 = (safe_mul_func_uint8_t_u_u(((*l_423) = ((((*l_475) = p_46) , ((((+(safe_rshift_func_uint16_t_u_u(func_67(((((func_67(l_482, (*l_434), p_46, ((l_474[0] , (safe_rshift_func_uint16_t_u_s((g_166 || (safe_add_func_uint8_t_u_u((g_223 <= (((*l_414) = (safe_sub_func_uint32_t_u_u(0x00F694D5L, (g_250 < p_44)))) , 0x0CADL)), g_327[4]))), l_489))) > 0x97C101DCL)) | g_55[0][2]) == 0xC6D591657F0AEE74LL) ^ (*p_45)) , (void*)0), l_490, l_491, g_29[0]), g_274))) ^ g_98) >= p_44) , l_491)) ^ 18446744073709551606UL)), 0x36L)));
            }
        }
        if ((safe_mul_func_uint16_t_u_u(func_67(((1L >= ((~(safe_mul_func_uint8_t_u_u((p_44 , l_491), ((*l_414) = (safe_sub_func_int16_t_s_s((((+((safe_mul_func_int8_t_s_s((((*l_441) = (safe_mod_func_int64_t_s_s(p_44, (-5L)))) < (p_44 , (-1L))), (g_504 != &l_441))) ^ p_44)) & p_44) <= 0x18L), 0x633DL)))))) >= p_46)) , &p_46), (*l_432), l_506[3], g_327[4]), p_44)))
        {
            int32_t *l_507[5] = {&g_55[0][2], &g_77, &g_55[0][2], &g_77, &g_55[0][2]};
            int i;
            l_431 = p_46;
            return g_410;
        }
        else
        {
            int32_t l_527 = 0x2ED02F62L;
            int32_t *l_528 = &l_431;
            for (g_98 = 0; (g_98 < 39); g_98 = safe_add_func_int8_t_s_s(g_98, 1))
            {
                const int64_t l_510 = 0x66885BB0D3B04F82LL;
                return l_510;
            }
            for (p_46 = 0; (p_46 >= 32); p_46++)
            {
                int32_t *l_526 = (void*)0;
                l_527 |= (safe_mul_func_int16_t_s_s((((l_506[1] , p_46) & 0UL) == (safe_add_func_int8_t_s_s((safe_lshift_func_int8_t_s_s(((*l_414) = (((6L > (safe_div_func_int16_t_s_s((((safe_lshift_func_int16_t_s_s(((void*)0 != &g_357), 11)) >= g_240) < g_51), (safe_lshift_func_uint8_t_u_s((p_44 , 0x7BL), 4))))) <= l_506[3]) , g_223)), g_250)), g_525))), 0L));
                if (p_44)
                    break;
                l_528 = l_441;
            }
        }
        l_431 |= ((*g_170) != (*g_170));
        if (func_67(&g_240, p_45, (g_100[9][1][4] < (safe_sub_func_int16_t_s_s(g_223, ((void*)0 == p_45)))), ((safe_lshift_func_uint16_t_u_s(((l_533 <= 1UL) == (safe_sub_func_int16_t_s_s(p_46, 0x9B62L))), p_46)) , l_536[1][3])))
        {
            const uint64_t *l_537 = &g_29[1];
            uint32_t *l_538[9] = {(void*)0, &g_51, (void*)0, &g_51, (void*)0, &g_51, (void*)0, &g_51, (void*)0};
            int64_t *l_543[1][6] = {{&g_544, (void*)0, &g_544, (void*)0, &g_544, (void*)0}};
            const int32_t l_547 = 0xFA065884L;
            int32_t *l_548 = &g_77;
            int i, j;
            (*l_548) = (((((l_546 = (l_545 = func_67(l_472, l_537, func_67(func_56(l_538[1], p_44, (safe_sub_func_uint16_t_u_u(3UL, (safe_mod_func_int8_t_s_s(((void*)0 == l_472), p_44))))), &g_409, g_24, g_327[4]), g_327[1]))) >= 0xF3B11F8E3621BBABLL) >= g_274) < g_24) ^ l_547);
            if (l_471)
                break;
            for (g_166 = 27; (g_166 <= 12); --g_166)
            {
                int32_t *l_551 = &l_546;
                int32_t **l_552 = &l_551;
                int32_t **l_553 = &l_548;
            }
        }
        else
        {
            int32_t *l_558[7] = {(void*)0, (void*)0, (void*)0, (void*)0, (void*)0, (void*)0, (void*)0};
            uint64_t **l_559 = &l_433;
            int i;
            l_545 |= (safe_mul_func_uint8_t_u_u(func_67(&g_51, p_45, p_44, (func_67(&g_51, &g_29[1], ((*l_441)++), ((void*)0 == &l_423)) , g_223)), 5L));
            l_431 = (l_559 == (g_560 = g_560));
            if (((p_46 <= p_44) > 0UL))
            {
                int32_t **l_562 = &l_558[6];
                const int32_t l_563 = (-1L);
                int64_t **l_568[9] = {&g_443[0][1], &g_443[0][1], &g_443[0][1], &g_443[0][1], &g_443[0][1], &g_443[0][1], &g_443[0][1], &g_443[0][1], &g_443[0][1]};
                int i;
                (*l_562) = &l_546;
                l_431 &= (p_44 != (l_563 & (((p_44 == ((safe_div_func_uint32_t_u_u((func_67((func_67(&g_51, (*g_560), ((((*g_561) , ((void*)0 == l_568[1])) , (++(*l_423))) == (safe_sub_func_int32_t_s_s((l_545 = (l_546 = p_44)), l_413[6][2][2]))), g_250) , &p_46), p_45, p_44, p_46) && 0xAEL), g_77)) >= g_327[0])) , 0xDE4C97F87A1B26B8LL) , g_51)));
            }
            else
            {
                int32_t **l_573 = &l_558[0];
                int32_t **l_574 = (void*)0;
                int32_t **l_575 = &g_74[5];
                (*l_575) = ((*l_573) = (void*)0);
                if (p_44)
                    break;
            }
        }
    }
    for (g_77 = 0; (g_77 <= 3); g_77 += 1)
    {
        int32_t l_578 = (-1L);
        uint32_t *l_579 = &g_51;
        uint64_t **l_585 = (void*)0;
        int32_t l_586 = 1L;
        int32_t l_596[1][6][5] = {{{5L, 0xF61CFCEFL, 0xC73391C2L, 0xF61CFCEFL, 5L}, {5L, 0xF61CFCEFL, 0xC73391C2L, 0xF61CFCEFL, 5L}, {5L, 0xF61CFCEFL, 0xC73391C2L, 0xF61CFCEFL, 5L}, {5L, 0xF61CFCEFL, 0xC73391C2L, 0xF61CFCEFL, 5L}, {5L, 0xF61CFCEFL, 0xC73391C2L, 0xF61CFCEFL, 5L}, {5L, 0xF61CFCEFL, 0xC73391C2L, 0xF61CFCEFL, 5L}}};
        int i, j, k;
        if (g_29[(g_77 + 1)])
            break;
        for (g_98 = 0; (g_98 <= 1); g_98 += 1)
        {
            int32_t * const l_576[8][8][1] = {{{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}, {{(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}, {(void*)0}}};
            int32_t **l_577 = &g_74[5];
            int64_t *l_580 = (void*)0;
            int64_t *l_581 = (void*)0;
            uint16_t *l_587 = &g_337;
            uint32_t l_588 = 1UL;
            int8_t l_597[9][7] = {{4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}, {4L, 1L, 0L, 0L, 1L, 4L, 4L}};
            int32_t l_598 = 0x39ABC6E6L;
            const uint64_t *l_604 = &g_24;
            int32_t l_609 = (-1L);
            uint16_t l_621[8][6];
            int i, j, k;
            for (i = 0; i < 8; i++)
            {
                for (j = 0; j < 6; j++)
                    l_621[i][j] = 65528UL;
            }
            (*l_577) = l_576[7][6][0];
            if ((l_588 ^= (((*l_587) &= (((l_578 |= p_44) != (func_67(l_579, g_443[g_98][(g_98 + 2)], (((l_582[0][3] = 0x9DCBD1F45CB97ED7LL) != (safe_sub_func_uint32_t_u_u((((g_55[0][2] , &p_45) != l_585) == (l_586 = ((void*)0 != &p_44))), 0L))) > 0x78L), g_55[0][8]) > 1UL)) ^ p_46)) , p_46)))
            {
                return g_274;
            }
            else
            {
                int32_t **l_590[5] = {&g_589, &g_589, &g_589, &g_589, &g_589};
                int64_t l_594 = 0L;
                int8_t l_600 = 0x88L;
                uint8_t l_601 = 6UL;
                int i;
                l_591 = ((*l_577) = g_589);
                l_601--;
            }
            if (func_67(&g_223, l_604, g_410, ((--(*l_579)) , ((((p_46 , ((safe_mod_func_int32_t_s_s(((*p_45) & p_46), (-1L))) , (void*)0)) != g_610) < p_46) == 0x531DL))))
            {
                uint8_t *l_620[2];
                uint8_t **l_619 = &l_620[0];
                int i;
                for (i = 0; i < 2; i++)
                    l_620[i] = &g_166;
                if (p_44)
                    break;
                (*l_577) = ((0x280F2F9CL > (0x1EFC6EDFL <= ((*g_589) = (safe_mul_func_int8_t_s_s((safe_add_func_int32_t_s_s((safe_div_func_int16_t_s_s((l_619 != (p_46 , &g_371)), g_409)), l_621[1][5])), g_337))))) , l_622);
            }
            else
            {
                int32_t l_625 = 1L;
                (*l_591) = (safe_add_func_uint64_t_u_u(l_625, 0x790B3243AF87AB82LL));
            }
        }
    }
    return g_240;
}







static uint64_t * func_47(uint32_t p_48)
{
    uint64_t *l_53 = &g_29[1];
    int32_t *l_54 = &g_55[0][2];
    int32_t l_232 = 0x497B5192L;
    int32_t l_233[7] = {0x902E5CEDL, 0x902E5CEDL, 8L, 0x902E5CEDL, 0x902E5CEDL, 8L, 0x902E5CEDL};
    uint8_t l_338[1];
    const uint8_t *l_374 = (void*)0;
    const uint8_t **l_373 = &l_374;
    int64_t l_377 = 0x6ED9E3C75212FEA3LL;
    int32_t *l_399 = &l_233[1];
    uint32_t *l_400[2];
    int32_t *l_405 = &l_232;
    int i;
    for (i = 0; i < 1; i++)
        l_338[i] = 7UL;
    for (i = 0; i < 2; i++)
        l_400[i] = &g_223;
    if (((*l_54) = ((((*l_53) &= 18446744073709551612UL) == 18446744073709551615UL) , p_48)))
    {
        uint32_t *l_72 = &g_51;
        const uint64_t *l_73[1][3];
        int32_t *l_231[5] = {&g_55[0][8], &g_55[0][2], &g_55[0][8], &g_55[0][2], &g_55[0][8]};
        int32_t **l_255[3][9][8] = {{{&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}}, {{&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}}, {{&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}, {&g_74[5], &l_231[4], &l_54, &l_54, &g_74[5], &l_231[1], &g_74[3], &l_231[1]}}};
        int i, j, k;
        for (i = 0; i < 1; i++)
        {
            for (j = 0; j < 3; j++)
                l_73[i][j] = &g_29[4];
        }
        for (p_48 = 0; (p_48 <= 0); p_48 += 1)
        {
            int8_t l_234 = 0x47L;
            int32_t l_235 = (-1L);
            int32_t l_239[4] = {0x8DAD69DFL, 3L, 0x8DAD69DFL, 3L};
            int i;
            for (g_51 = 0; (g_51 <= 0); g_51 += 1)
            {
                uint32_t *l_60[4] = {(void*)0, &g_51, (void*)0, &g_51};
                int32_t **l_230 = &g_74[5];
                int32_t l_236 = 0xC6DD85AFL;
                int32_t l_237 = 0x6AF6D611L;
                int32_t l_238[3][10][3] = {{{(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}}, {{(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}}, {{(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}, {(-1L), 0x15A0E331L, 0xA0861D2BL}}};
                int i, j, k;
                (*l_230) = func_56(l_60[2], (4294967289UL ^ ((safe_add_func_int32_t_s_s(g_55[p_48][(g_51 + 4)], (safe_sub_func_int16_t_s_s(func_67(l_72, l_73[0][1], g_55[p_48][g_51], g_55[0][2]), p_48)))) > p_48)), p_48);
                (*l_230) = l_231[1];
                g_240++;
            }
        }
        for (g_223 = 6; (g_223 != 3); g_223 = safe_sub_func_int8_t_s_s(g_223, 2))
        {
            uint16_t l_254 = 0x7C6BL;
            for (p_48 = 0; (p_48 <= 0); p_48 += 1)
            {
                int8_t *l_249[5][1];
                int32_t l_251 = 0x51C2BFEAL;
                uint32_t *l_252 = &g_100[1][0][3];
                const uint64_t **l_253 = &l_73[0][1];
                int i, j;
                for (i = 0; i < 5; i++)
                {
                    for (j = 0; j < 1; j++)
                        l_249[i][j] = &g_250;
                }
                l_233[4] = (g_77 ^= ((*l_54) = (safe_sub_func_uint32_t_u_u(func_67(l_231[1], ((*l_253) = ((safe_mul_func_int16_t_s_s(g_163, ((l_251 ^= g_24) , (~(((((*l_252) = (g_250 != (func_67(l_54, &g_24, ((*l_252) ^= ((p_48 , (&g_166 == &g_166)) < p_48)), (*l_54)) == p_48))) , 0x7F9CC139L) , p_48) || p_48))))) , (void*)0)), l_254, g_55[0][2]), 1L))));
            }
        }
        g_74[5] = &g_77;
    }
    else
    {
        uint8_t *l_262 = &g_166;
        uint8_t **l_263 = &l_262;
        const uint64_t *l_264[6][4][6];
        int32_t l_265 = 0x529E1FA4L;
        uint32_t *l_266 = &g_98;
        uint32_t *l_267 = &g_100[9][1][4];
        int32_t l_275 = (-3L);
        int32_t l_294[1];
        int8_t l_296 = 4L;
        uint32_t l_297[7][2] = {{0xADA9A81FL, 0xEE314A90L}, {0xADA9A81FL, 0xEE314A90L}, {0xADA9A81FL, 0xEE314A90L}, {0xADA9A81FL, 0xEE314A90L}, {0xADA9A81FL, 0xEE314A90L}, {0xADA9A81FL, 0xEE314A90L}, {0xADA9A81FL, 0xEE314A90L}};
        uint64_t l_308 = 0x9A4CDCF968874FEFLL;
        uint32_t *l_316 = &l_297[3][1];
        int64_t l_366 = 0xFD129FD41D7B5927LL;
        int i, j, k;
        for (i = 0; i < 6; i++)
        {
            for (j = 0; j < 4; j++)
            {
                for (k = 0; k < 6; k++)
                    l_264[i][j][k] = &g_24;
            }
        }
        for (i = 0; i < 1; i++)
            l_294[i] = 0x1B184DC0L;
lbl_343:
        if ((safe_mod_func_uint8_t_u_u((((*l_267) = ((*l_266) ^= (safe_rshift_func_int16_t_s_s(((func_67(&g_223, ((((void*)0 == &p_48) | (safe_mul_func_int8_t_s_s((((*l_263) = l_262) != &g_166), (*l_54)))) , l_264[4][0][2]), l_265, g_100[3][0][4]) > 65535UL) | 0x1FE3246DL), p_48)))) == (*l_54)), g_55[0][2])))
        {
            const uint8_t l_272 = 254UL;
            int64_t *l_273 = &g_274;
lbl_276:
            l_275 &= ((*l_54) = (g_166 == ((safe_sub_func_uint16_t_u_u(0x330DL, (safe_sub_func_int16_t_s_s((p_48 || (g_55[0][2] == ((*l_273) = (func_67(l_266, l_53, l_265, (((g_250 , (-1L)) | (-2L)) || (-1L))) != l_272)))), p_48)))) >= (*l_54))));
            for (g_163 = 0; (g_163 <= 4); g_163 += 1)
            {
                int64_t **l_278 = &l_273;
                int64_t ***l_277 = &l_278;
                if (l_275)
                    goto lbl_276;
                (*l_277) = (void*)0;
            }
        }
        else
        {
            int32_t *l_279 = (void*)0;
            int32_t *l_280 = &l_232;
            int32_t *l_281 = &l_232;
            int8_t l_282 = 0x72L;
            int32_t *l_283 = (void*)0;
            int32_t *l_284 = &g_77;
            int32_t *l_285 = &g_55[0][2];
            int32_t *l_286 = &l_275;
            int32_t *l_287 = &l_265;
            int32_t *l_288 = &l_233[4];
            int32_t l_289 = 0L;
            int32_t *l_290 = &l_275;
            int32_t *l_291 = &g_55[0][0];
            int32_t *l_292 = &l_233[1];
            int32_t *l_293[4];
            int16_t l_295 = (-1L);
            int i;
            for (i = 0; i < 4; i++)
                l_293[i] = &g_77;
            ++l_297[3][1];
            (*l_284) = (safe_add_func_uint8_t_u_u((safe_mod_func_uint16_t_u_u((((func_67(&g_51, &g_29[2], (safe_div_func_int64_t_s_s(g_77, g_166)), (((safe_sub_func_int8_t_s_s((g_223 == (*l_291)), (g_166 && l_308))) , (safe_unary_minus_func_uint8_t_u(((g_223 < g_98) == g_240)))) | p_48)) > 0x72L) ^ p_48) == (*l_280)), (-6L))), 248UL));
        }
        for (l_296 = (-12); (l_296 >= (-26)); l_296 = safe_sub_func_uint32_t_u_u(l_296, 9))
        {
            int16_t l_339 = 0x5D9FL;
            int32_t l_353 = (-1L);
            uint32_t *l_363 = &g_223;
            uint8_t l_369[2];
            const uint8_t ***l_375 = &l_373;
            int8_t l_381[7];
            int32_t l_382 = 0x683EA0A8L;
            int32_t l_383 = 0L;
            const uint64_t *l_387[5];
            int i;
            for (i = 0; i < 2; i++)
                l_369[i] = 0x0CL;
            for (i = 0; i < 7; i++)
                l_381[i] = 0x41L;
            for (i = 0; i < 5; i++)
                l_387[i] = &g_29[0];
            for (l_308 = 0; (l_308 != 45); l_308 = safe_add_func_int32_t_s_s(l_308, 6))
            {
                uint32_t *l_315[8];
                uint32_t **l_314[10][4][6] = {{{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}, {{(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}, {(void*)0, &l_315[1], &l_315[4], &l_315[0], &l_315[4], &l_315[1]}}};
                int32_t l_323[1][3];
                uint16_t *l_326 = &g_327[4];
                uint16_t *l_336[10][7][3] = {{{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}, {{&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}, {&g_337, &g_337, &g_337}}};
                uint8_t *l_342 = &l_338[0];
                int i, j, k;
                for (i = 0; i < 8; i++)
                    l_315[i] = &l_297[2][0];
                for (i = 0; i < 1; i++)
                {
                    for (j = 0; j < 3; j++)
                        l_323[i][j] = 0xAEF7B459L;
                }
                g_74[5] = (l_54 = func_56((l_316 = &l_297[1][1]), ((safe_rshift_func_uint8_t_u_u((safe_lshift_func_uint16_t_u_s(((((*l_54) = 0xED038F22L) || (safe_div_func_uint16_t_u_u(l_323[0][0], (safe_mod_func_uint8_t_u_u(((-1L) != ((((*l_326) = 65535UL) | (+((p_48 != ((*l_54) = (g_337 = (safe_rshift_func_uint8_t_u_u((l_323[0][0] , (safe_mul_func_int8_t_s_s((safe_lshift_func_int8_t_s_u((safe_mul_func_uint8_t_u_u(((void*)0 != &g_51), g_274)), 2)), p_48))), 5))))) < p_48))) > 0L)), p_48))))) > l_338[0]), 4)), p_48)) && g_77), l_323[0][0]));
                g_74[0] = func_56(func_56(&g_51, func_67((l_316 = func_56(&p_48, l_339, g_337)), &g_24, l_339, (p_48 & (((safe_sub_func_int16_t_s_s(g_337, g_51)) , l_342) != (void*)0))), l_308), p_48, p_48);
                if (g_240)
                    goto lbl_343;
            }
            for (g_240 = 18; (g_240 >= 41); g_240 = safe_add_func_int8_t_s_s(g_240, 4))
            {
                int8_t l_346 = 0xD6L;
                uint32_t *l_349 = &g_51;
                uint16_t *l_352[3];
                int64_t *l_354[10][10] = {{&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}, {&g_274, &g_274, (void*)0, (void*)0, &g_274, &g_274, (void*)0, &g_274, (void*)0, &g_274}};
                int16_t *l_355 = (void*)0;
                int16_t *l_356 = &g_357;
                int32_t **l_358[1][3];
                int i, j;
                for (i = 0; i < 3; i++)
                    l_352[i] = &g_327[3];
                for (i = 0; i < 1; i++)
                {
                    for (j = 0; j < 3; j++)
                        l_358[i][j] = &g_74[1];
                }
                g_74[0] = func_56(func_56(&g_223, func_67((l_346 , ((safe_rshift_func_uint16_t_u_s(func_67(l_349, (((l_346 & ((*l_356) &= ((l_294[0] = (safe_sub_func_uint16_t_u_u((l_353 = (l_346 == 0x197B71F3110B7B52LL)), g_223))) , func_67(&l_297[3][1], (l_339 , l_354[4][0]), p_48, l_294[0])))) <= 0x1AL) , l_354[7][8]), p_48, p_48), p_48)) , (void*)0)), &g_24, l_339, g_327[4]), g_223), g_327[4], g_337);
            }
            l_233[0] ^= func_67(&l_297[5][0], l_53, (*l_54), (safe_mod_func_int64_t_s_s(((safe_rshift_func_int8_t_s_u(func_67(l_363, &g_24, ((safe_mod_func_uint16_t_u_u(1UL, g_29[3])) ^ g_55[0][5]), g_163), g_55[0][0])) >= 1UL), l_366)));
            if (func_67(((((safe_div_func_int64_t_s_s((p_48 <= l_369[0]), (*l_54))) , (g_370 == ((*l_375) = l_373))) , (g_166 ^ l_296)) , &g_51), l_53, p_48, p_48))
            {
                int32_t *l_376 = &l_353;
                int32_t *l_378 = &g_77;
                int32_t *l_379[10][2] = {{(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}, {(void*)0, (void*)0}};
                int64_t l_380 = 3L;
                uint64_t l_384 = 0xB3AF85561B8B1E9ELL;
                int i, j;
                l_384--;
            }
            else
            {
                uint16_t *l_392 = (void*)0;
                uint16_t *l_393 = &g_327[4];
                int32_t *l_396 = &l_232;
                (*l_396) |= ((func_67(l_363, l_387[3], (((*l_393) = (func_67(&l_297[3][1], l_387[0], (safe_sub_func_uint64_t_u_u((l_383 = (safe_mul_func_int16_t_s_s(l_297[3][1], (((**l_263) |= (((g_98 <= g_100[9][1][4]) ^ 0xA750DB596FCD1235LL) < ((*l_393)++))) , ((&l_373 == &g_370) <= 0xF155211B66BD0EFFLL))))), 18446744073709551614UL)), p_48) > 0x259FA338E81CB12FLL)) , 0xCA52EC5AL), g_240) , 0xD998B90FL) , 0x6F2A60F1L);
                l_383 = 0x0670CA06L;
                if (p_48)
                    continue;
                (*l_54) = p_48;
            }
        }
    }
    (*l_399) = (safe_mul_func_uint8_t_u_u(0xBDL, 0x5EL));
    (*l_405) |= (func_67(func_56(l_400[0], (*l_399), ((safe_rshift_func_int16_t_s_s((p_48 | (safe_mod_func_int64_t_s_s((*l_399), g_29[1]))), 1)) >= func_67(&g_51, l_53, g_163, g_51))), &g_24, p_48, p_48) || (*l_399));
    return l_53;
}







static int32_t * func_56(uint32_t * p_57, int64_t p_58, int64_t p_59)
{
    int16_t l_89 = (-1L);
    uint16_t l_90 = 65528UL;
    const uint64_t *l_93 = &g_29[3];
    uint32_t *l_96 = &g_51;
    int32_t l_113 = 0x9A5ABFD0L;
    uint32_t *l_129 = &g_100[9][1][4];
    int16_t l_160 = 8L;
    int32_t l_178 = 0xE9BA2161L;
    int32_t l_179 = 0xFEEB18F6L;
    int32_t l_181 = 0xB8902181L;
    int32_t l_182 = 0xFDD04435L;
    int32_t l_183 = 0L;
    int32_t l_184 = 0xD4E822E7L;
    int32_t l_185 = 1L;
    int32_t l_186 = 0xE851F445L;
    int32_t l_188 = 0x42EEF4D9L;
    int32_t l_190 = 5L;
    int32_t **l_211[9][2][3] = {{{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}, {{(void*)0, &g_74[5], (void*)0}, {(void*)0, &g_74[5], (void*)0}}};
    int32_t l_212 = (-1L);
    uint32_t l_224 = 4294967295UL;
    uint64_t l_229 = 0x45E9BEFF2D9E755FLL;
    int i, j, k;
lbl_165:
    for (p_59 = 0; (p_59 <= 11); p_59 = safe_add_func_int32_t_s_s(p_59, 1))
    {
        uint32_t *l_84 = &g_51;
        const uint64_t *l_85 = &g_29[0];
        int32_t l_88 = 1L;
        uint32_t *l_92 = &g_51;
        uint32_t **l_91 = &l_92;
        uint32_t *l_97 = &g_98;
        uint32_t *l_99 = &g_100[9][1][4];
        if ((func_67(l_84, l_85, ((*l_99) = (((safe_sub_func_uint32_t_u_u((((*l_97) = ((l_88 & (l_89 >= (l_90 = 0x7E9E582DL))) == func_67(((*l_91) = p_57), l_93, (((safe_add_func_uint8_t_u_u(g_51, func_67(l_96, &g_24, g_29[1], p_58))) , l_89) == g_29[1]), g_29[1]))) != 0x12ABB1EFL), 0xF6804519L)) | 0x73E4L) != l_88)), l_89) , 0xB313CF36L))
        {
            int32_t **l_101 = &g_74[5];
            int32_t *l_102[8][2][10] = {{{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}, {{&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}, {&g_55[0][2], &g_55[0][5], (void*)0, &g_77, &g_77, &g_55[0][2], &l_88, (void*)0, &l_88, &g_55[0][2]}}};
            int i, j, k;
            (*l_101) = l_96;
            (*l_101) = l_102[6][0][2];
        }
        else
        {
            const int32_t l_105 = 0x4FEF296FL;
            uint64_t *l_109[8][1];
            int32_t *l_116[9][5] = {{&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}, {&g_55[0][6], &l_113, &g_55[0][6], &l_113, &g_55[0][6]}};
            int i, j;
            for (i = 0; i < 8; i++)
            {
                for (j = 0; j < 1; j++)
                    l_109[i][j] = &g_29[4];
            }
            for (l_90 = 2; (l_90 < 5); ++l_90)
            {
                int32_t *l_106 = &g_55[0][3];
                uint64_t *l_107 = (void*)0;
                uint64_t **l_108[8][3][8] = {{{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}, {{(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}, {(void*)0, &l_107, (void*)0, (void*)0, &l_107, &l_107, &l_107, &l_107}}};
                int16_t *l_112 = &l_89;
                int i, j, k;
                if (p_58)
                    break;
                if (l_105)
                    break;
                (*l_106) = l_88;
                l_113 = func_67(l_96, &g_29[2], (((l_109[5][0] = l_107) == (l_105 , l_85)) && (safe_mul_func_int16_t_s_s(((*l_112) = g_55[0][7]), func_67(l_106, l_109[5][0], (g_55[0][8] , 4294967294UL), p_58)))), l_88);
            }
            l_113 |= (safe_add_func_uint32_t_u_u(l_88, g_24));
            l_88 = l_88;
            return &g_55[0][0];
        }
    }
    for (g_77 = 8; (g_77 > 25); ++g_77)
    {
        uint64_t l_123[2];
        uint32_t *l_128 = &g_100[9][1][4];
        uint32_t **l_127[3][5][4] = {{{&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}}, {{&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}}, {{&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}, {&l_128, &l_128, &l_128, &l_128}}};
        uint64_t *l_134 = &g_29[0];
        uint64_t *l_137[8];
        int32_t *l_138 = (void*)0;
        int32_t *l_139 = &g_55[0][0];
        int32_t l_176[7][5] = {{0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}, {0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}, {0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}, {0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}, {0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}, {0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}, {0x9A08780BL, 0x9A08780BL, 0x48D3402EL, 1L, 0x50707C83L}};
        uint64_t l_204 = 0x15FF56717282AEC8LL;
        int i, j, k;
        for (i = 0; i < 2; i++)
            l_123[i] = 0UL;
        for (i = 0; i < 8; i++)
            l_137[i] = (void*)0;
        for (p_59 = (-21); (p_59 > 20); p_59++)
        {
            for (l_90 = 0; (l_90 == 58); l_90 = safe_add_func_uint32_t_u_u(l_90, 1))
            {
                int32_t *l_124 = &g_55[0][4];
                (*l_124) ^= l_123[0];
            }
            if (p_59)
                break;
            if (l_90)
                break;
        }
        if (((*l_139) = ((((((safe_add_func_int8_t_s_s(((l_90 , (l_129 = l_96)) == &g_100[0][1][0]), ((safe_mod_func_int8_t_s_s((g_24 > (((*l_134) ^= (safe_add_func_uint32_t_u_u(g_55[0][2], 0x1BC1FB24L))) <= ((((l_113 = (safe_lshift_func_int16_t_s_u(g_55[0][2], 5))) ^ func_67(p_57, &g_24, l_123[1], p_59)) >= g_100[9][1][4]) > p_58))), p_59)) > l_90))) ^ 0L) ^ l_90) , 0xF0C6F357L) >= p_59) != g_24)))
        {
            const int64_t l_146 = 0L;
            const uint64_t *l_153[7][7] = {{&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}, {&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}, {&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}, {&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}, {&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}, {&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}, {&g_29[1], &g_29[0], &g_29[1], &g_29[1], &g_24, &g_29[1], &g_29[1]}};
            int8_t *l_162 = &g_163;
            int32_t l_177 = 0xBFED9C38L;
            int32_t l_180 = 0xFDE322FCL;
            int32_t l_187 = 0x28DFF64AL;
            int32_t l_189 = 0xAC15ABFEL;
            int32_t l_191 = 0x7967E873L;
            int i, j;
            if (((safe_rshift_func_int8_t_s_s(g_100[9][1][4], 7)) > (safe_mod_func_uint16_t_u_u(((safe_add_func_uint32_t_u_u(l_146, (g_29[2] ^ ((*l_162) = (safe_add_func_int64_t_s_s(0xE715EE1BD5518D9DLL, ((safe_rshift_func_uint8_t_u_s(((safe_mod_func_int16_t_s_s((((*l_139) , ((((func_67(p_57, l_153[6][6], (safe_sub_func_int8_t_s_s((safe_add_func_uint16_t_u_u(((safe_rshift_func_uint8_t_u_u(((l_160 = p_58) > (safe_unary_minus_func_int8_t_s(p_59))), p_58)) == l_146), l_146)), g_24)), l_113) , g_55[0][2]) >= g_100[9][1][4]) >= g_55[0][2]) , l_146)) , 8L), (*l_139))) , p_58), g_29[3])) || 0x38165E96L))))))) , g_51), g_51))))
            {
                int32_t **l_164 = &l_139;
                (*l_164) = p_57;
                if (l_89)
                    goto lbl_165;
                if (g_166)
                    break;
            }
            else
            {
                const uint32_t l_169[3] = {4294967295UL, 4294967295UL, 4294967295UL};
                int32_t *l_173 = &g_55[0][2];
                int32_t *l_174 = (void*)0;
                int32_t *l_175[4][4][9] = {{{&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}}, {{&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}}, {{&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}}, {{&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}, {&l_113, (void*)0, &l_113, &g_77, &g_55[0][2], &g_55[0][2], &g_55[0][7], &g_77, &g_55[0][8]}}};
                uint8_t l_192 = 0xD2L;
                int i, j, k;
                (*l_139) = (safe_sub_func_int64_t_s_s((l_169[2] < p_58), ((void*)0 == g_170)));
                ++l_192;
            }
            if ((safe_div_func_int64_t_s_s(((p_59 & l_160) , 0x96437F609D877C5ELL), func_67(&g_51, &l_123[1], g_166, (p_59 && g_77)))))
            {
                l_187 = p_59;
                if (l_160)
                    goto lbl_165;
            }
            else
            {
                int16_t l_197[9][3][9] = {{{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}, {{(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}, {(-8L), 0xD878L, 0x7052L, 8L, 0x5876L, 0x914EL, (-5L), (-10L), 7L}}};
                int32_t *l_198 = &l_180;
                int i, j, k;
                if (l_197[0][0][5])
                    break;
                return p_57;
            }
        }
        else
        {
            uint64_t l_220 = 0UL;
            const int32_t *l_222 = &l_184;
            (*l_139) = ((safe_rshift_func_uint8_t_u_u(((safe_add_func_int16_t_s_s(((safe_unary_minus_func_int8_t_s(l_204)) , (-1L)), (safe_add_func_uint32_t_u_u((((((((++(*l_128)) >= p_58) , (*l_139)) , (safe_mul_func_int8_t_s_s(0x14L, (l_211[3][0][1] == (l_212 , l_211[8][0][2]))))) , ((void*)0 == l_139)) | g_55[0][2]) || g_166), 6UL)))) & p_58), g_55[0][2])) != p_58);
            for (g_98 = 0; (g_98 < 11); g_98 = safe_add_func_int32_t_s_s(g_98, 6))
            {
                uint8_t *l_219 = &g_166;
                int32_t l_221 = 0x8CD9B646L;
                l_222 = (((func_67(p_57, &g_24, g_100[3][1][0], p_59) || ((*l_134) = (((!(((((((*l_219) = ((safe_mod_func_int8_t_s_s(g_163, 8UL)) == (((*l_139) = (safe_add_func_int8_t_s_s(((g_163 , 4294967293UL) , p_58), 255UL))) == 1UL))) , l_220) , l_221) != p_59) & g_77) < 0xADE1094DL)) || g_24) != l_220))) , p_58) , (void*)0);
                if (g_223)
                    continue;
            }
        }
        g_74[0] = (void*)0;
        l_224++;
    }
    if (g_77)
        goto lbl_165;
    for (l_185 = 0; (l_185 == 10); l_185 = safe_add_func_int16_t_s_s(l_185, 1))
    {
        for (l_181 = 1; (l_181 <= 4); l_181 += 1)
        {
            l_229 ^= p_58;
        }
        if (p_59)
            continue;
        return p_57;
    }
    return &g_77;
}







static int16_t func_67(uint32_t * p_68, const uint64_t * p_69, uint32_t p_70, const int32_t p_71)
{
    uint64_t *l_75 = &g_29[1];
    int32_t *l_76[5][1] = {{&g_77}, {&g_77}, {&g_77}, {&g_77}, {&g_77}};
    uint32_t l_78 = 4294967295UL;
    int32_t *l_79 = &g_55[0][0];
    int32_t **l_80 = (void*)0;
    int32_t **l_81 = &l_76[1][0];
    int i, j;
    g_74[5] = &g_55[0][2];
    l_78 = (l_75 == &g_24);
    (*l_81) = l_79;
    return g_55[0][1];
}





int main (int argc, char* argv[])
{
    int i, j, k;
    int print_hash_value = 0;
    if (argc == 2 && strcmp(argv[1], "1") == 0) print_hash_value = 1;
    platform_main_begin();
    crc32_gentab();
    func_1();
    func_25(2, 3);
    func_10(7, 14);
    func_13();
    func_14();
    func_15(1, 2, 3, 4, 5);
    for (i = 0; i < 3; i++)
    {
        transparent_crc(g_23[i], "g_23[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_24, "g_24", print_hash_value);
    for (i = 0; i < 5; i++)
    {
        transparent_crc(g_29[i], "g_29[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_51, "g_51", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        for (j = 0; j < 9; j++)
        {
            transparent_crc(g_55[i][j], "g_55[i][j]", print_hash_value);
            if (print_hash_value) printf("index = [%d][%d]\n", i, j);

        }
    }
    transparent_crc(g_77, "g_77", print_hash_value);
    transparent_crc(g_98, "g_98", print_hash_value);
    for (i = 0; i < 10; i++)
    {
        for (j = 0; j < 2; j++)
        {
            for (k = 0; k < 6; k++)
            {
                transparent_crc(g_100[i][j][k], "g_100[i][j][k]", print_hash_value);
                if (print_hash_value) printf("index = [%d][%d][%d]\n", i, j, k);

            }
        }
    }
    transparent_crc(g_163, "g_163", print_hash_value);
    transparent_crc(g_166, "g_166", print_hash_value);
    transparent_crc(g_172, "g_172", print_hash_value);
    transparent_crc(g_223, "g_223", print_hash_value);
    transparent_crc(g_240, "g_240", print_hash_value);
    transparent_crc(g_250, "g_250", print_hash_value);
    transparent_crc(g_274, "g_274", print_hash_value);
    for (i = 0; i < 7; i++)
    {
        transparent_crc(g_327[i], "g_327[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_337, "g_337", print_hash_value);
    transparent_crc(g_357, "g_357", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_372[i], "g_372[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_409, "g_409", print_hash_value);
    transparent_crc(g_410, "g_410", print_hash_value);
    transparent_crc(g_430, "g_430", print_hash_value);
    transparent_crc(g_525, "g_525", print_hash_value);
    transparent_crc(g_544, "g_544", print_hash_value);
    transparent_crc(g_599, "g_599", print_hash_value);
    transparent_crc(g_612, "g_612", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        transparent_crc(g_632[i], "g_632[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    for (i = 0; i < 9; i++)
    {
        transparent_crc(g_762[i], "g_762[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_826.f0, "g_826.f0", print_hash_value);
    transparent_crc(g_826.f1, "g_826.f1", print_hash_value);
    transparent_crc(g_826.f2, "g_826.f2", print_hash_value);
    transparent_crc(g_826.f3, "g_826.f3", print_hash_value);
    transparent_crc(g_826.f4, "g_826.f4", print_hash_value);
    transparent_crc(g_826.f5, "g_826.f5", print_hash_value);
    transparent_crc(g_827.f0, "g_827.f0", print_hash_value);
    transparent_crc(g_827.f1, "g_827.f1", print_hash_value);
    transparent_crc(g_827.f2, "g_827.f2", print_hash_value);
    transparent_crc(g_827.f3, "g_827.f3", print_hash_value);
    transparent_crc(g_827.f4, "g_827.f4", print_hash_value);
    transparent_crc(g_827.f5, "g_827.f5", print_hash_value);
    transparent_crc(g_828.f0, "g_828.f0", print_hash_value);
    transparent_crc(g_828.f1, "g_828.f1", print_hash_value);
    transparent_crc(g_828.f2, "g_828.f2", print_hash_value);
    transparent_crc(g_828.f3, "g_828.f3", print_hash_value);
    transparent_crc(g_828.f4, "g_828.f4", print_hash_value);
    transparent_crc(g_828.f5, "g_828.f5", print_hash_value);
    transparent_crc(g_829.f0, "g_829.f0", print_hash_value);
    transparent_crc(g_829.f1, "g_829.f1", print_hash_value);
    transparent_crc(g_829.f2, "g_829.f2", print_hash_value);
    transparent_crc(g_829.f3, "g_829.f3", print_hash_value);
    transparent_crc(g_829.f4, "g_829.f4", print_hash_value);
    transparent_crc(g_829.f5, "g_829.f5", print_hash_value);
    transparent_crc(g_830.f0, "g_830.f0", print_hash_value);
    transparent_crc(g_830.f1, "g_830.f1", print_hash_value);
    transparent_crc(g_830.f2, "g_830.f2", print_hash_value);
    transparent_crc(g_830.f3, "g_830.f3", print_hash_value);
    transparent_crc(g_830.f4, "g_830.f4", print_hash_value);
    transparent_crc(g_830.f5, "g_830.f5", print_hash_value);
    transparent_crc(g_831.f0, "g_831.f0", print_hash_value);
    transparent_crc(g_831.f1, "g_831.f1", print_hash_value);
    transparent_crc(g_831.f2, "g_831.f2", print_hash_value);
    transparent_crc(g_831.f3, "g_831.f3", print_hash_value);
    transparent_crc(g_831.f4, "g_831.f4", print_hash_value);
    transparent_crc(g_831.f5, "g_831.f5", print_hash_value);
    transparent_crc(g_832.f0, "g_832.f0", print_hash_value);
    transparent_crc(g_832.f1, "g_832.f1", print_hash_value);
    transparent_crc(g_832.f2, "g_832.f2", print_hash_value);
    transparent_crc(g_832.f3, "g_832.f3", print_hash_value);
    transparent_crc(g_832.f4, "g_832.f4", print_hash_value);
    transparent_crc(g_832.f5, "g_832.f5", print_hash_value);
    transparent_crc(g_833.f0, "g_833.f0", print_hash_value);
    transparent_crc(g_833.f1, "g_833.f1", print_hash_value);
    transparent_crc(g_833.f2, "g_833.f2", print_hash_value);
    transparent_crc(g_833.f3, "g_833.f3", print_hash_value);
    transparent_crc(g_833.f4, "g_833.f4", print_hash_value);
    transparent_crc(g_833.f5, "g_833.f5", print_hash_value);
    transparent_crc(g_841, "g_841", print_hash_value);
    transparent_crc(g_858, "g_858", print_hash_value);
    transparent_crc(g_867, "g_867", print_hash_value);
    transparent_crc(g_888.f0, "g_888.f0", print_hash_value);
    transparent_crc(g_888.f1, "g_888.f1", print_hash_value);
    transparent_crc(g_888.f2, "g_888.f2", print_hash_value);
    transparent_crc(g_888.f3, "g_888.f3", print_hash_value);
    transparent_crc(g_888.f4, "g_888.f4", print_hash_value);
    transparent_crc(g_888.f5, "g_888.f5", print_hash_value);
    transparent_crc(g_891, "g_891", print_hash_value);
    transparent_crc(g_973.f0, "g_973.f0", print_hash_value);
    transparent_crc(g_973.f1, "g_973.f1", print_hash_value);
    transparent_crc(g_973.f2, "g_973.f2", print_hash_value);
    transparent_crc(g_973.f3, "g_973.f3", print_hash_value);
    transparent_crc(g_973.f4, "g_973.f4", print_hash_value);
    transparent_crc(g_973.f5, "g_973.f5", print_hash_value);
    transparent_crc(g_1063.f0, "g_1063.f0", print_hash_value);
    transparent_crc(g_1063.f1, "g_1063.f1", print_hash_value);
    transparent_crc(g_1063.f2, "g_1063.f2", print_hash_value);
    transparent_crc(g_1063.f3, "g_1063.f3", print_hash_value);
    transparent_crc(g_1063.f4, "g_1063.f4", print_hash_value);
    transparent_crc(g_1063.f5, "g_1063.f5", print_hash_value);
    transparent_crc(g_1091, "g_1091", print_hash_value);
    transparent_crc(g_1095, "g_1095", print_hash_value);
    transparent_crc(g_1097, "g_1097", print_hash_value);
    transparent_crc(g_1109.f0, "g_1109.f0", print_hash_value);
    transparent_crc(g_1109.f1, "g_1109.f1", print_hash_value);
    transparent_crc(g_1109.f2, "g_1109.f2", print_hash_value);
    transparent_crc(g_1109.f3, "g_1109.f3", print_hash_value);
    transparent_crc(g_1109.f4, "g_1109.f4", print_hash_value);
    transparent_crc(g_1109.f5, "g_1109.f5", print_hash_value);
    transparent_crc(g_1117.f0, "g_1117.f0", print_hash_value);
    transparent_crc(g_1117.f1, "g_1117.f1", print_hash_value);
    transparent_crc(g_1117.f2, "g_1117.f2", print_hash_value);
    transparent_crc(g_1117.f3, "g_1117.f3", print_hash_value);
    transparent_crc(g_1117.f4, "g_1117.f4", print_hash_value);
    transparent_crc(g_1117.f5, "g_1117.f5", print_hash_value);
    transparent_crc(g_1150, "g_1150", print_hash_value);
    transparent_crc(g_1171, "g_1171", print_hash_value);
    transparent_crc(g_1195.f0, "g_1195.f0", print_hash_value);
    transparent_crc(g_1195.f1, "g_1195.f1", print_hash_value);
    transparent_crc(g_1195.f2, "g_1195.f2", print_hash_value);
    transparent_crc(g_1195.f3, "g_1195.f3", print_hash_value);
    transparent_crc(g_1195.f4, "g_1195.f4", print_hash_value);
    transparent_crc(g_1195.f5, "g_1195.f5", print_hash_value);
    transparent_crc(g_1232, "g_1232", print_hash_value);
    transparent_crc(g_1236, "g_1236", print_hash_value);
    transparent_crc(g_1273.f0, "g_1273.f0", print_hash_value);
    transparent_crc(g_1273.f1, "g_1273.f1", print_hash_value);
    transparent_crc(g_1273.f2, "g_1273.f2", print_hash_value);
    transparent_crc(g_1273.f3, "g_1273.f3", print_hash_value);
    transparent_crc(g_1273.f4, "g_1273.f4", print_hash_value);
    transparent_crc(g_1273.f5, "g_1273.f5", print_hash_value);
    transparent_crc(g_1323.f0, "g_1323.f0", print_hash_value);
    transparent_crc(g_1323.f1, "g_1323.f1", print_hash_value);
    transparent_crc(g_1323.f2, "g_1323.f2", print_hash_value);
    transparent_crc(g_1323.f3, "g_1323.f3", print_hash_value);
    transparent_crc(g_1323.f4, "g_1323.f4", print_hash_value);
    transparent_crc(g_1323.f5, "g_1323.f5", print_hash_value);
    for (i = 0; i < 8; i++)
    {
        transparent_crc(g_1340[i], "g_1340[i]", print_hash_value);
        if (print_hash_value) printf("index = [%d]\n", i);

    }
    transparent_crc(g_1399, "g_1399", print_hash_value);
    for (i = 0; i < 1; i++)
    {
        for (j = 0; j < 10; j++)
        {
            for (k = 0; k < 7; k++)
            {
                transparent_crc(g_1477[i][j][k], "g_1477[i][j][k]", print_hash_value);
                if (print_hash_value) printf("index = [%d][%d][%d]\n", i, j, k);

            }
        }
    }
    transparent_crc(g_1528, "g_1528", print_hash_value);
    platform_main_end(crc32_context ^ 0xFFFFFFFFUL, print_hash_value);
    return 0;
}
