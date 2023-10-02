// Nim version 2: In Jay Normal Form, debugging non-determinism

datatype Player = P1 | P2
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {
  && |v.piles| == 3
  && v.turn.P1? // syntax
}

// We re-write the v1 version using Jay Normal Form, putting all non-determinism
// into this Step datatype.
// DEMO: added NoOp step live
datatype Step =
  | TurnStep(take: nat, p: nat)
  | NoOpStep()

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep? // syntax for requiring this be a TurnStep
{
  // syntax: var in a function/predicate is immutable; it's just a shorthand to
  // make definitions more readable.
  // step.p accesses the p field of TurnStep. This is only legal because
  // `requires step.TurnStep?` ensures that constructor was used - NoOpStep
  // wouldn't have such a field.
  var p := step.p;
  var take := step.take;
  && p < |v.piles|
  && take <= v.piles[p]
  && v'.piles == v.piles[p := v.piles[p] - take]
     // DEMO: the same bug is here, but it'll be easier to debug
}

ghost predicate NoOp(v: Variables, v': Variables, step: Step)
  requires step.NoOpStep?
{
  v' == v
}

// nearly boilerplate (just gather up all transitions)
ghost predicate NextStep(v: Variables,  v': Variables, step: Step) {
  match step {
    case TurnStep(_, _) => Turn(v, v', step)
    case NoOpStep() => NoOp(v, v', step)
  }
}

// boilerplate - always the same
lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
{
  // DEMO: doesn't go through! let's debug it
  match step {
    case TurnStep(_, _) => {
      // DEMO: what part of variables isn't being specified deterministically?
      assert v'.piles == v''.piles;
      // this fails, at this point hopefully we realize we forgot to specify
      // turn entirely (if not, we'd add more assertions)
      assert v'.turn == v''.turn;
    }
    case NoOpStep() => {
      // no error here
      return;
    }
  }
}

// boilerplate - always the same
ghost predicate Next(v: Variables,  v': Variables) {
  exists step :: NextStep(v, v', step)
}
