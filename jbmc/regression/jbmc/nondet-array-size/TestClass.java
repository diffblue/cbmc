import org.cprover.CProver;

public class TestClass {

    public static void minimalJbmc(Object[] a) {
        CProver.assume(a != null && a.length > 1);
        float[] assigned = new float[a.length];
        assigned[0] = 1.0f;
        assert(false);
    }
}
