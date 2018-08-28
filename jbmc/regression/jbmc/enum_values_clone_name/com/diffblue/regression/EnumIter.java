package com.diffblue.regression;
public class EnumIter {
    void f() {
        MyEnum[] a = MyEnum.values();
        String s = a[2].name() + a[3].name();
        assert s.equals("CD");
    }
}
