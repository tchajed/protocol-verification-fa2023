ghost predicate IsSorted(s:seq<int>) {
  forall i:nat, j:nat | i < j < |s| :: s[i] <= s[j]
}

ghost predicate SearchIndex1(haystack: seq<int>, needle: int, i: nat)
{
  // && haystack[i-1] < needle
  // && haystack[i] <= needle
  && (i == 0 || (i-1 < |haystack| ==> haystack[i-1] < needle))
  && (i < |haystack| ==> haystack[i] >= needle)
  && (i == |haystack| ==> forall j:nat | j < |haystack| :: haystack[j] < needle)
     // && i <= |haystack|
}

lemma SearchIndex1Deterministic(haystack: seq<int>, needle: int, i1: nat, i2: nat)
  requires IsSorted(haystack)
  requires SearchIndex1(haystack, needle, i1)
  requires SearchIndex1(haystack, needle, i2)
  ensures i1 == i2
{}

ghost predicate SearchIndex2(haystack: seq<int>, needle: int, i: nat)
{
  && (forall j:nat | j < i < |haystack| :: haystack[j] <= needle)
  && (forall j:nat | i <= j < |haystack| :: haystack[j] >= needle)
  && i <= |haystack|
}

lemma SearchIndex2Deterministic(haystack: seq<int>, needle: int, i1: nat, i2: nat)
  requires IsSorted(haystack)
  requires SearchIndex2(haystack, needle, i1)
  requires SearchIndex2(haystack, needle, i2)
  ensures i1 == i2
{
}

lemma SeachIndex2NonDet() returns (haystack: seq<int>, needle: int, i1: nat, i2: nat)
  ensures IsSorted(haystack)
  ensures SearchIndex2(haystack, needle, i1)
  ensures SearchIndex2(haystack, needle, i2)
  ensures i1 != i2
{
  haystack := [1, 2, 2, 3];
  needle := 2;
  i1 := 1;
  i2 := 2;
}

ghost predicate SearchIndex3(haystack: seq<int>, needle: int, i: nat)
{
  && (forall j:nat | j < i < |haystack| :: haystack[j] < needle)
  && (forall j:nat | i <= j < |haystack| :: haystack[j] >= needle)
  && i <= |haystack|
  && (i == |haystack| ==> forall j:nat | j < |haystack| :: haystack[j] < needle)
}

lemma SearchIndex3Deterministic(haystack: seq<int>, needle: int, i1: nat, i2: nat)
  requires IsSorted(haystack)
  requires SearchIndex3(haystack, needle, i1)
  requires SearchIndex3(haystack, needle, i2)
  ensures i1 == i2
{
  if i2 == |haystack| {
    if i1 < |haystack| {
      assert haystack[i1] >= needle;
      assert haystack[i1-1] < needle;
    }
    return;
  }
  if i1 == |haystack| {
    if i2 < |haystack| {
      return;
    }
    return;
  }
  assert haystack[i1] >= needle;
  assert haystack[i2] >= needle;
  return;
}

method LinearSearch(haystack: seq<int>, needle: int) returns (index: nat)
  requires IsSorted(haystack)
  ensures SearchIndex3(haystack, needle, index)
{
  // not found
  if |haystack| == 0 {
    return |haystack|;
  }
  // found immediately
  if haystack[0] >= needle {
    return 0;
  }
  // search remainder
  var i' := LinearSearch(haystack[1..], needle);
  return 1 + i';
}

method LinearSearchLoop(haystack: seq<int>, needle: int) returns (index: nat)
  requires IsSorted(haystack)
  ensures SearchIndex3(haystack, needle, index)
{
  var i: nat := 0;
  while i < |haystack|
    invariant i <= |haystack|
    invariant forall j:nat | j < i :: haystack[j] < needle
  {
    if haystack[i] >= needle {
      return i;
    }
    i := i + 1;
  }
  return i;
}
