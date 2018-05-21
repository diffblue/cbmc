public class test {

    int field;

    public static void f() {

        test testinstance = new test();
        test testnull = null;
        int x = 0;
        try {
            x = testinstance.field;
        }
        catch(NullPointerException e) {
            x++;
        }
        try {
            x = testnull.field;
        }
        catch(NullPointerException e) {
            x++;
        }
    }

}
