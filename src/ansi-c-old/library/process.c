/* FUNCTION: _beginthread */

__CPROVER_size_t _beginthread( 
  void (*start_address)(void *),
  unsigned stack_size,
  void *arglist)
{
  __CPROVER_HIDE:;
  __CPROVER_ASYNC_1: start_address(arglist);
  (void)stack_size;
  __CPROVER_size_t handle;
  return handle;
}

/* FUNCTION: _beginthreadex */

__CPROVER_size_t _beginthreadex( 
   void *security,
   unsigned stack_size,
   unsigned (*start_address )(void *),
   void *arglist,
   unsigned initflag,
   unsigned *thrdaddr)
{
  __CPROVER_HIDE:;
  __CPROVER_ASYNC_1: start_address(arglist);
  if(security)
    (void)*(char*)security;
  (void)stack_size;
  (void)initflag;
  (void)*thrdaddr;
  __CPROVER_size_t handle;
  return handle;
}

