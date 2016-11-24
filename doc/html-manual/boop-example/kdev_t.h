#ifndef __KDEV_T_H__
#define __KDEV_T_H__

#define MINORBITS       8

typedef unsigned short kdev_t;

#define MAJOR(dev)      ((dev) >> MINORBITS)
#define MINOR(dev)      ((dev) % 256)
#define NODEV           0

typedef unsigned int mode_t;
typedef unsigned int loff_t;

struct inode {
  kdev_t i_rdev;
};

struct file {
  mode_t f_mode;
  loff_t f_pos;
};

struct data {
  int   size;
  char *content;
};

#endif
