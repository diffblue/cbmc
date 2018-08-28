package com.diffblue.regression;
public class EnumIter {
    void f() {
        MyEnum[] a = MyEnum.values();
        int num = a[2].ordinal() + a[3].ordinal();
        assert num == 5;
    }
}
