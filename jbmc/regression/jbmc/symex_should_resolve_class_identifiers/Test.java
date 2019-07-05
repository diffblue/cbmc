public class Test {

    public static class A {
        public int getInteger() {
            return 0;
        }
    }

    public static class B extends A {
        public int getInteger() {
            return 1;
        }
    }

    public static void test(A a) {
        // Need to instantiate B to make sure it's loaded
        B dummyB = new B();

        int zero = a.getInteger();
        assert(zero == 2);
    }

}
