import java.io.PrintStream;

public class MyHashMap {

    private Integer[] table;
    private int size;

    public MyHashMap() {
        table = new Integer[8];
        size = 0;
    }

    public void put(Integer key) {
        table[size++] = key;
    }

    public MySet entrySet() {
        return new EntrySet();
    }
    
    class EntrySet implements MySet {
        public final MyIterator iterator() {
            return new UselessIterator();
        }
    }

    class UselessIterator implements MyIterator {
        boolean b;
        UselessIterator() {
            b = true;
        }
        public boolean someBoolean() {
            return b;
        }
        public void next() {
            b = false;
        }
    }

    public MySet keySet() {
        return new KeySet();
    }

    class KeySet implements MySet {
        public final MyIterator iterator() {
            return new UselessIterator();
        }
    }

    public static boolean test() {
        MyHashMap hm = new MyHashMap();
        MySet es = hm.entrySet();
        MyIterator it = es.iterator();
        while (it.someBoolean()) {
            it.next();
        }
        return true;
    }

}
