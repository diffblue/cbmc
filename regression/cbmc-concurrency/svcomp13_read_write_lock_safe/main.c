/* Testcase from Threader's distribution. For details see:
   http://www.model.in.tum.de/~popeea/research/threader

   This file is adapted from the example introduced in the paper:
   Thread-Modular Verification for Shared-Memory Programs
   by Cormac Flanagan, Stephen Freund, Shaz Qadeer.
*/

int w=0, r=0, x, y;

void __VERIFIER_atomic_take_write_lock() {
  __VERIFIER_assume(w==0 && r==0);
  w = 1;
}

void __VERIFIER_atomic_take_read_lock() {
  __VERIFIER_assume(w==0);
  r = r+1;
}

void __VERIFIER_atomic_release_read_lock() {
  r = r-1;
}

void *writer() { //writer
  __VERIFIER_atomic_take_write_lock();
  x = 3;
  w = 0;
}

void *reader() { //reader
  int l;
  __VERIFIER_atomic_take_read_lock();
  l = x;
  y = l;
  assert(y == x);
  __VERIFIER_atomic_release_read_lock();
}

int main() {
__CPROVER_ASYNC_1: writer();
__CPROVER_ASYNC_2:
  reader();
__CPROVER_ASYNC_3:
  writer();
__CPROVER_ASYNC_4:
  reader();
  return 0;
}
