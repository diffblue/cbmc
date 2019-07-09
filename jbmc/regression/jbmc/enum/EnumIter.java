public class EnumIter {
    void f() {
        MyEnum[] a = MyEnum.values();
        int num = a[2].ordinal() + a[3].ordinal();
        assert num == 5;
    }

    void name() {
        MyEnum[] a = MyEnum.values();
        String s = a[2].name() + a[3].name();
        assert s.equals("CD");
    }
}
