#include "driver.h"

int usecount;
int dummy_major;

int register_chrdev (unsigned int major, const char* name)
{
  usecount = 0;
  if (major == 0)
    return MAJOR_NUMBER;
  return major;
}

int unregister_chrdev (unsigned int major, const char* name)
{
  if (MOD_IN_USE)
    {
    ERROR: __CPROVER_assert(0, "MOD_IN_USE in unregister_chrdev");
    }
  else
    return 0;
}

int main ()
{
  int            rval;
  int            size;
  struct file    my_file;
  char          *buffer; /* we do not model this buffer */
  struct inode   inode;
  unsigned int   count;
  unsigned char  random;

  int lock_held = 0; 

  dummy_major = register_chrdev (0, "dummy");
  inode.i_rdev = dummy_major << MINORBITS;

  init_module ();

  /* assign arbitrary values */
  my_file.f_mode = nondet_uint ();
  my_file.f_pos  = nondet_uint ();

  do
    {
      random = nondet_uchar ();
      __CPROVER_assume (0 <= random && random <= 3);

      switch (random)
	{
	case 1: 
	  rval = dummy_open (&inode, &my_file);
	  if (rval == 0)
	    lock_held = TRUE;
	  break;
	case 2:
	  __CPROVER_assume (lock_held);
	  count = dummy_read (&my_file, buffer, BUF_SIZE); 
	  break;
	case 3:
	  dummy_release (&inode, &my_file);
	  lock_held = FALSE;
	  break;
	default:
	  break;
	}
    }
  while (random || lock_held);

  cleanup_module ();
  unregister_chrdev (dummy_major, "dummy");

  return 0;
}
