extern int __VERIFIER_nondet_int();
/* Testcase from Threader's distribution. For details see:
   http://www.model.in.tum.de/~popeea/research/threader

   This file is adapted from the Promela code introduced in the paper:
   Using Promela and Spin to verify parallel algorithms
   by Paul McKenney
*/

int idx=0; // boolean to control which of the two elements will be used by readers
  // (idx <= 0) then ctr1 is used
  // (idx >= 1) then ctr2 is used
int ctr1=1, ctr2=0;
int readerprogress1=0, readerprogress2=0; // the progress is indicated by an integer:
  // 0: reader not yet started
  // 1: reader withing QRCU read-side critical section
  // 2: reader finished with QRCU read-side critical section

void __VERIFIER_atomic_use1(int myidx) {
  __VERIFIER_assume(myidx <= 0 && ctr1>0);
  ctr1++;
}

void __VERIFIER_atomic_use2(int myidx) {
  __VERIFIER_assume(myidx >= 1 && ctr2>0);
  ctr2++;
}

void __VERIFIER_atomic_use_done(int myidx) {
  if (myidx <= 0) { ctr1--; }
  else { ctr2--; }
}

void __VERIFIER_atomic_take_snapshot(int *readerstart1, int *readerstart2) {
  /* Snapshot reader state. */
  *readerstart1 = readerprogress1;
  *readerstart2 = readerprogress2;
}

void __VERIFIER_atomic_check_progress1(int readerstart1) {
  /* Verify reader progress. */
  if (__VERIFIER_nondet_int()) {
    __VERIFIER_assume(readerstart1 == 1 && readerprogress1 == 1);
    assert(0);
  }
  return;
}

void __VERIFIER_atomic_check_progress2(int readerstart2) {
  if (__VERIFIER_nondet_int()) {
    __VERIFIER_assume(readerstart2 == 1 && readerprogress2 == 1);
    assert(0);
  }
  return;
}

void *qrcu_reader1() {
  int myidx;
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (__VERIFIER_nondet_int()) {
      __VERIFIER_atomic_use1(myidx);
      break;
    } else {
      if (__VERIFIER_nondet_int()) {
	__VERIFIER_atomic_use2(myidx);
	break;
      } else {}
    }
  }
  readerprogress1 = 1;
  readerprogress1 = 2;
  /* rcu_read_unlock */
  __VERIFIER_atomic_use_done(myidx);
  return 0;
}

void *qrcu_reader2() {
  int myidx;
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (__VERIFIER_nondet_int()) {
      __VERIFIER_atomic_use1(myidx);
      break;
    } else {
      if (__VERIFIER_nondet_int()) {
	__VERIFIER_atomic_use2(myidx);
	break;
      } else {}
    }
  }
  readerprogress2 = 1;
  readerprogress2 = 2;
  /* rcu_read_unlock */
  __VERIFIER_atomic_use_done(myidx);
  return 0;
}

void* qrcu_updater() {
  int i;
  int readerstart1, readerstart2;
  int sum;
  __VERIFIER_atomic_take_snapshot(&readerstart1, &readerstart2);
  sum = ctr2;
  sum = sum + ctr1;
  if (sum > 1) {
    if (idx <= 0) { ctr2++; idx = 1; ctr1--; }
    else { ctr1++; idx = 0; ctr2--; }
    if (idx <= 0) { __CPROVER_assume (ctr1 <= 0); }
    else { __CPROVER_assume (ctr2 <= 0); }
  } else {}
  __VERIFIER_atomic_check_progress1(readerstart1);
  __VERIFIER_atomic_check_progress2(readerstart2);
  return 0;
}

int main() {
__CPROVER_ASYNC_1: qrcu_reader1();
__CPROVER_ASYNC_2: qrcu_reader2();
__CPROVER_ASYNC_3: qrcu_updater();
  return 0;
}
