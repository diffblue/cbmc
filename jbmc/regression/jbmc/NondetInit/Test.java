import org.cprover.CProver;

class Test {
    int size;
    int[] data1;
    int[] data2;

    void cproverNondetInitialize() {
        // This specifies invariants about object of this class.
        // This avoids finding spurious bugs.
        CProver.assume(data1 != null && data2 != null && size == data1.length + data2.length);
    }

    int check(int x) {
        int i;
        if(x >= size || x < 0)
            return -1;

        assert(data1 != null || data2 == null);

        if (x >= data1.length) {
            i = x - data1.length;
            assert(i < data2.length);
            return data2[i];
        } else {
            assert(x < data1.length);
            return data1[x];
        }

    }
}
