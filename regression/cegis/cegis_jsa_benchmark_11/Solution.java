package com.javarush.test.level08.lesson08.task02;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/* Удалить все числа больше 10
Создать множество чисел(Set<Integer>), занести туда 20 различных чисел.
Удалить из множества все числа больше 10.
*/

public class Solution
{
    public static HashSet<Integer> createSet()
    {
        HashSet<Integer> set = new HashSet<Integer>();
        for (int i = 0; i < 20; i++)
            set.add((int) (i * 2.3456));
        return set;
    }

    public static HashSet<Integer> removeAllNumbersMoreThan10(HashSet<Integer> set)
    {
        Iterator<Integer> it = set.iterator();
        while (it.hasNext())
        {
            Integer temp = it.next();
            if (temp > 10)
                it.remove();
        }

        return set;
    }

}
