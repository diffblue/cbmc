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

interface J
{
    int getANumber();
}

class C implements J {
    public int c;
    public int getANumber() { return c; }
}

class D implements J {
    public int d;
    public int getANumber() { return d; }
}

class TestClass
{
    public I someObject1;
    public J someObject2;

    public boolean foo() {
        if(someObject1 != null && someObject2 != null)
        {
            if(someObject1.getANumber() == someObject2.getANumber()) {
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
        // ensure that A, B, C, D are referenced explicitly
        // in order to get them converted into GOTO
        A a = new A();
        B b = new B();
        C c = new C();
        D d = new D();
    }
}
