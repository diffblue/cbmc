package com.diffblue.regression;
public class EnumIter {
    String f() {
        MyEnum[] a = MyEnum.values();
        return a[2].name() + a[3].name();
    }
}
