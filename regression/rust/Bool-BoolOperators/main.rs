fn main() {
  assert!(true);
  assert!(true || false);
  assert!(!false);

  let a = true;
  let b = false;
  let c = a || b;
  let d = c && a;
  assert!(d && true);
  assert!(!b && d);

  let e : bool;
  assert!(e || !e);
}
