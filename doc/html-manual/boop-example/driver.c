#include "driver.h"

extern int dummy_major;
int locked;

int init_module (void)
{
  locked = FALSE;
}

void cleanup_module (void) { }

int dummy_open (struct inode *inode, struct file *filp)
{
  __CPROVER_assert(MAJOR (inode->i_rdev) == dummy_major, "i_rdev mismatch");
  MOD_INC_USE_COUNT;

  if (locked)
    return -1;
  locked = TRUE;
 
  return 0; /* success */
}

unsigned int dummy_read (struct file *filp, char *buf, int max)
{
  int n;
  if (locked)
    {
      n = nondet_int ();
      __CPROVER_assume ((n >= 0) && (n <= max));
      /* writing to the buffer is not modeled here */
      
      return n;
    }
  return -1;
}

int dummy_release (struct inode *inode, struct file *filp)
{
  if (locked)
    {
      MOD_DEC_USE_COUNT;
      locked = FALSE;
      return 0;
    }
  return -1;
}

