class B extends RuntimeException {}

class A {
    int i;
}

public class Test {
    public static void main(String args[]) {
        A a=null;
        try {
            int i=a.i;
        }
        catch (NullPointerException exc) {
            assert false;
        }
    }
}
