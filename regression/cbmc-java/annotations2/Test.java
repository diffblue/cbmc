@interface FieldAnnotation {
}

public class Test {
    @FieldAnnotation
    public static double d;

    public void check() {
        double f = d;
        assert(f == d);
        assert(f != d);
    }
}
