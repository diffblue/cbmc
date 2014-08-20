/*
 * Recursive implementation multiplication by repeated addition
 * Check that this multiplication is commutative
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

extern int __VERIFIER_nondet_int(void);

// Multiplies two integers n and m
int mult(int n, int m) {
    if (m < 0) {
        return mult(n, -m);
    }
    if (m == 0) {
        return 0;
    }
    return n + mult(n, m - 1);
}

int main() {
    int m = __VERIFIER_nondet_int();
    if (m < 0 || m > 46340) {
        return 0;
    }
    int n = __VERIFIER_nondet_int();
    if (n < 0 || n > 46340) {
        return 0;
    }
    int res1 = mult(m, n);
    int res2 = mult(n, m);
    if (res1 != res2 && m > 0 && n > 0) {
        ERROR:
        goto ERROR;
    } else {
        return 0;
    }
}
