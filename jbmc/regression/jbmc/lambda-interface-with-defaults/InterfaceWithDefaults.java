interface InterfaceWithDefaults {

  public int f(int x);

  public default int g() { return 1; }
}
