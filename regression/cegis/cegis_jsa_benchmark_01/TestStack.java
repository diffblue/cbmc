package net.sinjax.techinterview.collection;

import static org.junit.Assert.*;

import java.util.Iterator;

import org.junit.Test;

public class TestStack {
	@Test public void testStack(){
		Stack<Integer> s = new LinkedListStack<Integer>();
		for(int i = 0; i < 10; i++){
			s.push(i);
		}
		for(int i = 9; i >=0; i--){
			assertTrue(new Integer(i).equals(s.peek()));
			assertTrue(new Integer(i).equals(s.pop()));
			assertTrue(!new Integer(i).equals(s.peek()));
		}
		
		for(int i = 0; i < 10; i++){
			s.push(i);
		}
		int expecting = 9;
		for(Integer i : s){
			assertTrue((new Integer(expecting--)).equals(i));
		}
		
		Integer toRemove = 5;
		Iterator<Integer> it = s.iterator();
		for(;!it.hasNext();){
		{
			Integer i = it.next();
			if(i.equals(toRemove)){
				it.remove();
			}
		}
		for(Integer i : s){
			assertTrue(!(new Integer(toRemove)).equals(i));
		}
				
		}
		
	}
}
