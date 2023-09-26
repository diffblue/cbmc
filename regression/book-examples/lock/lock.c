_Bool nondet_bool();
unsigned int nondet_unsigned_int();
_Bool LOCK = 0;

_Bool lock()
{
  if(nondet_bool())
  {
    assert(!LOCK);
    LOCK = 1;
    return 1;
  }

  return 0;
}

void unlock()
{
  assert(LOCK);
  LOCK = 0;
}

int main()
{
  unsigned got_lock = 0;
  unsigned times = nondet_unsigned_int();

  while(times > 0)
  {
    if(lock())
    {
      got_lock++;
      /* critical section */
    }

    if(got_lock != 0)
      unlock();

    got_lock--;
    times--;
  }
}
