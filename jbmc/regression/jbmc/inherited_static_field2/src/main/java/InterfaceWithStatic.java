import java.util.ArrayList;

interface InterfaceWithStatic {

  // The ArrayList is only here to define a constant x that
  // is complicated enough for javac to generate a static init
  // rather than just propagate the constant to all users.
  static ArrayList<Integer> al = new ArrayList<Integer>();
  static int x = al.size();

}

