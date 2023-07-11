class Sorted {
  var xs: seq<int>
  ghost var min: int
}

ghost predicate IsSorted(s: Sorted)
  reads s
{
  (forall i, j :: 0 <= i <= j < |s.xs| ==> s.xs[i] <= s.xs[j]) &&
  (s.xs != [] ==> s.xs[0] == s.min)
}

method sum(s: Sorted) returns (res: int)
  requires IsSorted(s)
  ensures IsSorted(s)
  ensures res >= s.min * |s.xs|
  // modifies s
{
  res := 0;

  for index := 0 to |s.xs|
    invariant res >= s.min * index
  {
    res := res + s.xs[index];
  }
}

method Nice(s: Sorted)
  requires IsSorted(s)
  // modifies s
{
  var a := sum(s);
  var b := sum(s);
  assert s.xs == old(s.xs);
}
