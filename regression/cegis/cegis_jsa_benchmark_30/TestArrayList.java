package test;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class TestArrayList {
	
	public static void main(String[] args) {
		ArrayList<Integer> strs = new ArrayList<Integer>();
		for(int i=0; i<10; i++) {
			strs.add(i);
		}
		
		for(Integer i : strs) {
			if(i % 2 == 0)
				strs.remove(i);
		}
		
		for(Integer i : strs) {
			System.out.println(i);
		}
	}
	
	//�����ķ���
	public void removeEvensVer(List<Integer> lst) {
		Iterator<Integer> itr = lst.iterator();
		
		while( itr.hasNext()) 
			if(itr.next()%2 == 0) 
				itr.remove();
	}

}
