import java.util.*;

public class Question3_5{
	public static void main(String[] args){
		MyQueue mq = new MyQueue();
		mq.add(1);
		mq.add(2);
		mq.add(3);
		mq.add(4);
		mq.remove();
		mq.add(5);
		System.out.print(mq.remove() + " ");
		mq.add(6);
	}
}
class MyQueue{
	Deque<Integer> addStack = new LinkedList<Integer>();
	Deque<Integer> removeStack = new LinkedList<Integer>();

	public void add(Integer i){//not thread safe
		move(removeStack, addStack);
		addStack.push(i);
	}

	public Integer remove(){//not thread safe
		if (removeStack.size() == 0 && addStack.size() == 0){
			throw new NoSuchElementException();
		}
		move(addStack, removeStack);
		return removeStack.pop();
	}

	private void move(Deque<Integer> from, Deque<Integer> to){
		if (from.size() == 0) return;
		if (to.size() > 0) throw new IllegalStateException();
		Iterator<Integer> it = from.iterator();
		while(it.hasNext()){
			to.push(it.next());
			it.remove();	
		}
	}
}
