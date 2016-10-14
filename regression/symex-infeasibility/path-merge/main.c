
	#define SIZE 15
	#include <assert.h>

	int main() {
		int A[1];
		int x;
		int i = 0;
		int v1 = 0;
		int v2 = 0;
		int p1 = 0;
		int p2 = 0;

		int N = 8;
		int y;

		for(i = 0; i < N; i++) {
			if(x) {
				p1 = p1 + 1;
			} else {
				p2 = p2 + 1;
			}
		}


		if(x) {
			y = y + 1;
		} else {
			y = y - 1;
		}

		if(x) {
			y = 1;
		} else{
			y = 2;
		}

		assert(y == 1 || y == 2);

		for(i = 0; i < N; i++) {
			if(x) {
				p1 = p1 + 1;
			} else {
				p2 = p2 + 1;
			}
		}


		i = 0;
		assert( p1 + p2 ==  2*N);

		/*
			Results
				Normal: 105.656s.  0 SAT.
				Runtime: 6.856s total, 1.064s SAT

				1060 variables, 3801 clauses
		*/
	}
