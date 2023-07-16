class Sorted {
  var xs: seq<int>
  ghost var min: int
  ghost predicate IsSorted() reads this {
    (forall i, j :: 0 <= i <= j < |xs| ==> xs[i] <= xs[j]) &&
    (xs != [] ==> xs[0] == min)
  }
}

method sum(s: Sorted) returns (res: int)
  requires s.IsSorted()
  ensures s.IsSorted()
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
  requires s.IsSorted()
  // modifies s
{
  var a := sum(s);
  var b := sum(s);
  assert s.xs == old(s.xs);
}
