unsigned int nondet_int();

int bsy;

void main();
int client_thread1();
int client_thread2();

void main() {
	bsy = 0;
	__CPROVER_ASYNC_1: client_thread1();
	__CPROVER_ASYNC_2: client_thread2();
}

int client_thread1() {
	bsy = 1;
	bsy = 0;
}

int client_thread2() {
	__CPROVER_atomic_begin();
	if (nondet_int()) {
		__CPROVER_assume(bsy == 0);
	} else {
		__CPROVER_assume(!(bsy == 0));

		assert (bsy);
	}
	__CPROVER_atomic_end();
}
