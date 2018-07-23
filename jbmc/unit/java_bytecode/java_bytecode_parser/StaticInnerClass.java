public class StaticInnerClass {
    public static interface SomeInterface {
        public int i = 0;
    }
    public static class PublicStaticInnerClass {
        public int i;
        public PublicStaticInnerClass(int i) {
            this.i = i;
        }
    }
    public class PublicNonStaticInnerClass {
        public int i;
        public PublicNonStaticInnerClass(int i) {
            this.i = i;
        }
    }
    public static SomeInterface staticAnonymousClass = new SomeInterface() {
        public int i = 50;
    };
    public SomeInterface anonymousClass = new SomeInterface() {
        public int i = 25;
    };
    public void testNonStatic() {
        class LocalClassInNonStatic {
            public int i = 1;
        }
    }
    public static void testStatic() {
        class LocalClassInStatic {
            public int i = 2;
        }
    }
}
