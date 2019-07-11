fn main() {
  let a : i32;
  let b = -a;

  if a > 0 {
    assert!(a > b);
  }
  else if a < 0 {
    assert!(a < b - 1);
  }
  else {
    assert!(b == a);
  }
}
