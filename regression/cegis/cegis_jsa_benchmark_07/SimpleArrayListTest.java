package com.lysongzi.test;

import java.util.Iterator;

import org.junit.Test;

import com.lysongzi.collection.SimpleArrayList;

public class SimpleArrayListTest {
	private SimpleArrayList<Integer> sal;
	
	@Test
	public void test() {
		sal = new SimpleArrayList<Integer>();
		for(int i=10; i > 0; i--)
			sal.append(i);
		System.out.println(sal);
		
		//删除前两个元素
		sal.remove(0);
		sal.remove(0);
		System.out.println(sal);
		
		//调用迭代器删除剩余元素中的所有偶数
		for(Iterator<Integer> it = sal.iterator(); it.hasNext();){
			Integer num = it.next();
			//删除所有偶数
			if(num%2 == 0)
				it.remove();
		}
		System.out.println(sal);
	}

}
