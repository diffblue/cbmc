public enum Equality {
  FOO,
  BAR;

  public int check(boolean assertionCheck) {
    if (this.equals(FOO)) {
      assert !assertionCheck;
      return 0;
    }
    return 1;
  }
  
  public int withTypecast(boolean assertionCheck) {
    if (this.equals((Object)FOO)) {
      assert !assertionCheck;
      return 0;
    }
    return 1;
  }
}
