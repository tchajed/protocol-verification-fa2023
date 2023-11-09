module UtilitiesLibrary {
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  function {:opaque} UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {
    if |theSets| == 0 then {}
    else UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  // As you can see, Dafny's recursion heuristics easily complete the recursion
  // induction proofs, so these two statements could easily be ensures of
  // UnionSeqOfSets. However, the quantifiers combine with native map axioms
  // to be a bit trigger-happy, so we've pulled them into independent lemmas
  // you can invoke only when needed.
  // Suggestion: hide calls to this lemma in an
  //   assert P by { SetsAreSubsetsOfUnion(...) }
  // construct so you can get your conclusion without "polluting" the rest of the
  // lemma proof context with this enthusiastic forall.
  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx |
              0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
    reveal_UnionSeqOfSets();
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
              exists idx {:trigger member in theSets[idx]} :: 0<=idx<|theSets| && member in theSets[idx]
  {
    reveal UnionSeqOfSets();
  }

  lemma UnionSeqOfSets_auto<T>()
    ensures forall theSets: seq<set<T>> {:trigger UnionSeqOfSets(theSets)} ::
              forall idx |
                0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
    ensures  forall theSets: seq<set<T>> ::
               forall member | member in UnionSeqOfSets(theSets) ::
                 exists idx {:trigger member in theSets[idx]} :: 0<=idx<|theSets| && member in theSets[idx]
  {
    forall theSets: seq<set<T>>
      ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
      ensures forall member | member in UnionSeqOfSets(theSets) ::
                exists idx {:trigger member in theSets[idx]} :: 0<=idx<|theSets| && member in theSets[idx]
    {
      SetsAreSubsetsOfUnion(theSets);
      EachUnionMemberBelongsToASet(theSets);
    }
  }

  // Convenience function for learning a particular index (invoking Hilbert's
  // Choose on the exists in EachUnionMemberBelongsToASet).
  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {
    EachUnionMemberBelongsToASet(theSets);
    var chosenIdx :| 0<=chosenIdx<|theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }

  datatype Option<T> = Some(value:T) | None

  function MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
  {
    map j | j in m && j != key :: m[j]
  }
}
