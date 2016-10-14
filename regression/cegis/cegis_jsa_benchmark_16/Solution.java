package com.javarush.test.level08.lesson08.task02;

import java.util.HashSet;
import java.util.Iterator;

/* Удалить все числа больше 10
Создать множество чисел(Set<Integer>), занести туда 20 различных чисел.
Удалить из множества все числа больше 10.
*/

public class Solution
{



    public static HashSet<Integer> createSet()
    {
        HashSet<Integer> hs = new HashSet<Integer>();

        for (int i=0;i<20;i++){
         hs.add(i+i);
        }

        return hs;
    }

    public static HashSet<Integer> removeAllNumbersMoreThen10(HashSet<Integer> set)
    {

        Iterator<Integer> it = set.iterator();

        while (it.hasNext()){
            if (it.next()>10) it.remove();
        }

        return set;

    }
}
