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
		
		//ɾ��ǰ����Ԫ��
		sal.remove(0);
		sal.remove(0);
		System.out.println(sal);
		
		//���õ�����ɾ��ʣ��Ԫ���е�����ż��
		for(Iterator<Integer> it = sal.iterator(); it.hasNext();){
			Integer num = it.next();
			//ɾ������ż��
			if(num%2 == 0)
				it.remove();
		}
		System.out.println(sal);
	}

}
