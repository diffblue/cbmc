class B extends RuntimeException {}

class A {
    int i;
}

public class Test {
    public static void main(String args[]) {
        A a=null;
        try {
            a.i=0;
            // TODO: an explicit throw is currently needed in order
            // for CBMC to convert the exception handler
            throw new B();
        }
        catch (NullPointerException exc) {
            assert false;
        }
    }
}
