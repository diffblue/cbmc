import org.cprover.CProver;

class Test {

    int[] arr;

    void cproverNondetInitialize() {
        CProver.assume(arr != null && arr.length == 1);
        // The following access should now be legal:
        arr[0] = 100;
    }

    public static void main(Subclass nondetInput) {
        // The condition enforced by cproverNondetInitialize should hold
        // even though the parameter is a subtype of Test, not directly an
        // instance of Test itself.
        if(nondetInput != null)
            assert nondetInput.arr.length == 1;
    }

}

class Subclass extends Test { }
