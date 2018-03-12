import java.util.function.*;

public class Lambdatest {

    class A {
        int x;
    }

    CustomLambda<Integer> custom = x -> true;
    BiFunction<Float, Integer, Integer> add = (x0, y0) -> x0.intValue() + y0;
    int z = 10;

    A a;
    B b = new B();

    public Integer g(Float x, Integer y, BiFunction<Float, Integer, Integer> fun) {
        return fun.apply(x, y);
    }

    public int f(Float x, Integer y, Integer z) {
        Integer tmp = add.apply(x, y);
        Function<Integer, Integer> mul = (a) -> a * tmp;
        return mul.apply(z);
    }

    public int i(int x) {
        int z = 5;
        Function<Integer, Integer> foo = (a) -> a * z;
        return foo.apply(x);
    }

    public int j(int x) {
        Function<Integer, Integer> foo = (a) -> a * z;
        return foo.apply(x);
    }

    public int k(int x) {
        a.x = 10;
        
        Function<Integer, Integer> foo = (y) -> y * a.x;
        return foo.apply(x);
    }
    
    public int l(int x) {
        b.y = 10;
        Function<Integer, Integer> foo = (y) -> {
            int r = y * b.y;
            b.set(r);
            return r;
        };
        b = new B();
        b.y = 14;
        return foo.apply(x);
    }

    public int m(int x) {
        b.y = 10;
        Function<Integer, Integer> foo = (y) -> {
            int r = y * b.y;
            b.y = r;
            return r;
        };
        return foo.apply(x);
    }

    // test static field of different class
    public double d(Double x) {
        return B.dmul.apply(x);
    }

    public int capture2(Float a) {
        return add.apply(a, 1);
    }

    public boolean custom(Integer i) {
        return custom.is_ok(i);
    }
}

class C implements CustomLambda<Integer> {
    public boolean is_ok(Integer i) {
        return true;
    }
}
