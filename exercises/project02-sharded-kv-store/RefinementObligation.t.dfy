// This module defines the lemmas we're going to prove in RefinementProof.v.dfy.
// The use of a dafny abstract module (and its companion, module "refinement")
// allows us to separate out this _trusted_ statement from the _verified_ proof
// in the other file.

include "AtomicKV.t.dfy"
include "DistributedSystem.t.dfy"

abstract module RefinementObligation {
  import opened UtilitiesLibrary
  import opened Types
  import opened DistributedSystem
  import AtomicKV

  ghost function VariablesAbstraction(v: Variables) : AtomicKV.Variables
    requires v.WF()

  ghost predicate Inv(v: Variables)

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures AtomicKV.Init(VariablesAbstraction(v))

  lemma RefinementNext(v: Variables, v': Variables, event: Event)
    requires Next(v, v', event)
    requires Inv(v)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
}
