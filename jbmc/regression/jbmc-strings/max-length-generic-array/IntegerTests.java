public class IntegerTests {

    public static Boolean testMyGenSet(Integer key) {
        if (key == null) return null;
        MyGenSet<Integer> ms = new MyGenSet<>();
        ms.array = new Integer[1];
        ms.array[0] = 101;
        if (ms.contains(key)) {
          assert false;
          return true;
        }
        assert false;
        return false;
    }

    public static Boolean testMySet(Integer key) {
        if (key == null) return null;
        MySet ms = new MySet();
        ms.array[0] = 101;
        if (ms.contains(key)) {
          assert false;
          return true;
        }
        assert false;
        return false;
    }

}

class MyGenSet<E> {
    E[] array;
    MyGenSet() {
      // Note the caller must instantiate the array as generic array creation
      // is illegal (the compiler doesn't statically know the type to allocate)
    }
    boolean contains(E o) {
        if (o.equals(array[0]))
            return true;
        return false;
    }
}

class MySet {
    Integer[] array;
    MySet() {
        array = new Integer[1];
    }
    boolean contains(Integer o) {
        if (o.equals(array[0]))
            return true;
        return false;
    }
}
