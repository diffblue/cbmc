interface I
{
    int getANumber();
}

class A implements I {
    public int a;

    public int getANumber() { return a; }
}

class B implements I {
    public int b;
    public int getANumber() { return b; }
}

class TestClass
{
    public static boolean foo(I someObject) {
        if(someObject!=null)
        {
            int result = someObject.getANumber();
            if(result == 42) {
                return true;
            } else {
                return false;
            }
        }
        else
        {
            return false;
        }
    }

    public static void main(String[] args)
    {
        // ensure that A, B are referenced explicitly
        // in order to get them converted into GOTO
        A a = new A();
        B b = new B();
    }
}
