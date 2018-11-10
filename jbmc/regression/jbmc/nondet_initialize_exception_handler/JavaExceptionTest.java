public class JavaExceptionTest {

    public static Fake getFake() {
        try {
            return org.cprover.CProver.nondetWithoutNull((Fake)null);
        }
        catch(Exception t) {
            // Should be reachable due to exception thrown in
            // nondet-initialize:
            return new Fake();
        }
    }

    void test () {

        Fake a = null;
        try {
            a = getFake();
        }
        catch(Exception t) {
            // Should be unreachable
            assert false;
        }

    }

}

class Fake {
    protected final void cproverNondetInitialize() throws Exception {
        throw new Exception("Oh dear oh dear");
    }
}
