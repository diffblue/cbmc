class B {
    int j;
}

class A {
    int i;
    B b;
}

public class missing_class1 {
    public static void main(String[] args) {
	A a = new A();
	B b = a.b;
	int j = b.j; // NULL pointer dereference
    }
}
