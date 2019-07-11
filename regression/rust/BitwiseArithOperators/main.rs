fn main() {
  assert!(3 | 5 == 7);
  assert!(7 & 9 == 1);
  assert!(9 ^ 7 == 14);
  assert!(!8 ^ !0 == 8);

  let x = 1;
  let a : u32;
  let b : u32;
  let c = a + b;
  if c & x == x {
    let d = a ^ b;
    assert!(d & x == x);
  }
  else {
    assert!(a & x == b & x)
  }
}
