package com.diffblue.regression;
public class EnumIter {
    int f() {
        MyEnum[] a = MyEnum.values();
        int num = a[2].ordinal() + a[3].ordinal();
        return num ;
    }
}
