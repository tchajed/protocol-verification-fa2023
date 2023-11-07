// Analogous to ch04/invariant_proof.dfy, we show what the conditions on a
// refinement (an abstraction function, invariant, an initial condition, and an
// inductive property)

module Types {
  type Event(==, 0, !new)
}

import opened Types

module Code {
  import opened Types
  type Variables(==, 0, !new)
  ghost predicate Init(v: Variables)
  ghost predicate Next(v: Variables, v': Variables, ev: Event)

  ghost predicate IsBehavior(e: nat -> Event) {
    exists ss: nat -> Variables ::
      && Init(ss(0))
      && forall n: nat :: Next(ss(n), ss(n + 1), e(n))
  }
}

module Spec {
  import opened Types
  type Variables(==, 0, !new)
  ghost predicate Init(v: Variables)
  ghost predicate Next(v: Variables, v': Variables, ev: Event)

  ghost predicate IsBehavior(e: nat -> Event) {
    exists ss: nat -> Variables ::
      && Init(ss(0))
      && forall n: nat :: Next(ss(n), ss(n + 1), e(n))
  }
}

// The proof of refinement is based on supplying these two pieces of data. Note
// that they don't appear in the final statement of Refinement; they're only the
// evidence that shows how to demonstrate refinement one step at a time.

ghost predicate Inv(v: Code.Variables)
ghost function Abstraction(v: Code.Variables): Spec.Variables

lemma {:axiom} AbstractionInit(v: Code.Variables)
  requires Code.Init(v)
  ensures Inv(v)
  ensures Spec.Init(Abstraction(v))

lemma {:axiom} AbstractionInductive(v: Code.Variables, v': Code.Variables, ev: Event)
  requires Inv(v)
  requires Code.Next(v, v', ev)
  ensures Inv(v')
  ensures Spec.Next(Abstraction(v), Abstraction(v'), ev)

lemma InvAt(e: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires Code.Init(ss(0))
  requires forall k:nat :: Code.Next(ss(k), ss(k + 1), e(k))
  ensures Inv(ss(i))
{
  if i == 0 {
    AbstractionInit(ss(0));
  } else {
    InvAt(e, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), e(i - 1));
  }
}

lemma RefinementTo(e: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires forall n: nat :: Code.Next(ss(n), ss(n + 1), e(n))
  requires forall n: nat :: Inv(ss(n))
  ensures
    var ss' := (j: nat) => Abstraction(ss(j));
    && forall n: nat | n < i :: Spec.Next(ss'(n), ss'(n + 1), e(n))
{
  if i == 0 {
    return;
  } else {
    var ss' := (j: nat) => Abstraction(ss(j));
    RefinementTo(e, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), e(i - 1));
    AbstractionInductive(ss(i), ss(i+1), e(i));
    assert Spec.Next(ss'(i), ss'(i + 1), e(i));
  }
}

lemma Refinement(e: nat -> Event)
  requires Code.IsBehavior(e)
  ensures Spec.IsBehavior(e)
{
  var ss: nat -> Code.Variables :|
    && Code.Init(ss(0))
    && forall n: nat :: Code.Next(ss(n), ss(n + 1), e(n));
  forall i: nat
    ensures Inv(ss(i)) {
    InvAt(e, ss, i);
  }

  var ss': nat -> Spec.Variables :=
    (i: nat) => Abstraction(ss(i));
  assert Spec.Init(ss'(0)) by {
    AbstractionInit(ss(0));
  }
  forall n: nat
    ensures Spec.Next(ss'(n), ss'(n + 1), e(n))
  {
    RefinementTo(e, ss, n+1);
  }
}
