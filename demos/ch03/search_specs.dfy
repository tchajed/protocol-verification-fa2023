// In this file we'll explore some specifications for binary search. We won't
// have a definition, so we'll just write predicates that capture the
// BinarySearch ensures clause, and then reason about those predicates on their
// own.

ghost predicate IsSorted(s:seq<int>) {
  forall i:nat, j:nat | i < j < |s| :: s[i] <= s[j]
}

ghost predicate SearchIndex1(haystack: seq<int>, needle: int, i: nat)
{
  // DEMO: some people tried to write predicates that morally looked like the
  // comments. To make this plan actually work and handle all edge cases
  // requires a much more complicated definition, too complicated for a
  // specification for my taste (it's very easy to get this wrong).
  // && haystack[i-1] < needle
  // && haystack[i] <= needle
  && (i == 0 || (i-1 < |haystack| ==> haystack[i-1] < needle))
  && (i < |haystack| ==> haystack[i] >= needle)
  && (i == |haystack| ==> forall j:nat | j < |haystack| :: haystack[j] < needle)
     // DEMO: add this back to make SearchIndex1 deterministic
     // && i <= |haystack|
}

// One desirable property for binary search is to have a deterministic
// specification. This is especially the case for the assignment because it
// clarifies that if the needle is found multiple times, the lowest index should
// be returned.
lemma SearchIndex1Deterministic(haystack: seq<int>, needle: int, i1: nat, i2: nat)
  requires IsSorted(haystack)
  requires SearchIndex1(haystack, needle, i1)
  requires SearchIndex1(haystack, needle, i2)
  ensures i1 == i2
{}

// This is what I find a more elegant approach to capturing the same idea as the
// first attempt.
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

// DEMO: there's a bug in the above, because it says haystack[j] <= needle it
// allows any index that contains the needle, not just the smallest one.
//
// Here we prove the opposite of SearchIndex2Deterministic. Whereas that lemma
// is a proof for all values of haystack, needle, i1, and i2, here we show there
// _exists_ a counter-example, returning it from the lemma.
lemma SeachIndex2NonDet() returns (haystack: seq<int>, needle: int, i1: nat, i2: nat)
  ensures IsSorted(haystack)
  ensures SearchIndex2(haystack, needle, i1)
  ensures SearchIndex2(haystack, needle, i2)
  ensures i1 != i2
{
  // the crux is that the needle appears twice
  haystack := [1, 2, 2, 3];
  assert IsSorted(haystack);
  needle := 2;
  i1 := 1;
  i2 := 2;
}

// Here we fix that bug and also add another clause about exactly what happens
// if i == |haystack|. This is enough to make it deterministic, although as you
// can see below that proof wasn't so simple.
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
