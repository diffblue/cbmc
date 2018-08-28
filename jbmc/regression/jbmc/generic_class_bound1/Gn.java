interface A{}
interface B{}
interface C{}
interface L<T> extends A,B,C{}

public class Gn<T extends L<? extends B>>{
	Gn<?> ex1;
	public void foo1(Gn<?> ex1){
		if(ex1 != null)
		    this.ex1 = ex1;
		assert false;
	}
	public static void main(String[] args) {
		System.out.println("ddfsdf");
		assert false;
	}
}
