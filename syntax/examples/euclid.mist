pure fn gcd(x: Int, y: Int) -> Int
  requires x > 0, y > 0
  ensures
    result >= 1,
    divides(result, x),
    divides(result, y),
    forall(z: Int) if z >= 1 && divides(z, x) && divides(z, y) {
      z <= result
    };


macro divides_prop(x, y, z) { z >= 0 && x * z == y }

pure fn divides(x: Int, y: Int) -> Bool
  requires x > 0, y > 0
  ensures  result == exists(z: Int) divides_prop(x, y, z);


ghost fn lemma_show_divides(x: Int, y: Int, z: Int)
  requires x > 0, y > 0,
           divides_prop(x, y, z)
  ensures  divides(x, y);

ghost fn lemma_divides(x: Int, y: Int)
  requires x > 0, y > 0
  ensures  gcd(x + y, y) == gcd(x, y)
{
  lemma_gcd_lower(x, y);
  lemma_gcd_lower(x, y);
}

ghost fn lemma_gcd_upper(x: Int, y: Int)
  requires x > 0, y > 0
  ensures gcd(x + y, y) >= gcd(x, y)
{
  let z = x + y;
  let m = gcd(x + y, y);
  let n = gcd(y, x);

  let c = lemma_divides(n, y);
  let d = lemma_divides(n, x);

  lemma_show_divides(n, x + y, c + d);
}

ghost fn lemma_gcd_lower(x: Int, y: Int)
  requires x > 0, y > 0
  ensures gcd(x + y, y) <= gcd(x, y)
{
  let z = x + y;
  let m = gcd(x + y, y);

  let c = lemma_divides(m, z);
  let d = lemma_divides(m, y);

  lemma_show_divides(m, x, c - d);
}

ghost fn lemma_gcd_idempotent(x: Int)
  requires x > 0
  ensures gcd(x, x) == x
{
  lemma_show_divides(x, x, 1);
}

macro V(x, y) { x + y }

fn euclid(n: Int, m: Int) -> Int
  requires n > 0, m > 0
  ensures result == gcd(n, m)
{
  let a = m;
  let b = m;
  while a != b
    invariant a > 0, b > 0,
              gcd(a, b) == gcd(n, m)
  {
    if a > b {
      a = a - b;
      lemma_gcd(a, b);
    } else {
      b = b - a;
      lemma_gcd(b, a);
    }
  }

  assert a == b, gcd(a, b) == gcd(n, m);
  lemma_gcd_idempotent(a);
  assert gcd(n, m) == a;

  return a;
}
