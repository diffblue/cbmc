fn main() {
  let a : u32;
  let b = a / 2;
  assert!(b <= a);
  let c = b * 2;
  assert!(c >= b);
  let d = b + 5;
  let e = d + 1;
  assert!(e > d);
  let f = e - 2;
  assert!(f < d);
}
