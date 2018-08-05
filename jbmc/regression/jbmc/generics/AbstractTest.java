interface AbstractInt<K,V> { V get(); }

class AbstractImpl<K,V> implements AbstractInt<K,V> {
    V t;
    public V get() { return t; }
}

public class AbstractTest {
    class Dummy { private boolean b; }
    class ClassA { private int id; }
    class ClassB {
        private int id;
        int getId() { return id; }
    }

    public int getFromAbstract(AbstractImpl<ClassA, ClassB> arg) {
        if (arg == null)
            return -1;
        AbstractImpl<Dummy, Dummy> dummy = new AbstractImpl<>();
        ClassB b = arg.get();
        if (b == null)
            return -1;
        int i = b.getId();
        assert(i > 0);
        return i;
    }
}
