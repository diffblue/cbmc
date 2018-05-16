import org.cprover.CProver;

class Test {

    int[] arr;

    void cproverNondetInitialize() {
        CProver.assume(arr != null && arr.length == 1);
        // The following access should now be legal:
        arr[0] = 100;
    }

    public static void main(Test nondetInput) {
    }

}
