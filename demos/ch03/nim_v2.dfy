// Nim version 2: In Jay Normal Form, debugging non-determinism

datatype Player = P1 | P2
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {
  && |v.piles| == 3
  && v.turn.P1? // syntax
}

datatype Step = TurnStep(take: nat, p: nat)

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep? // syntax
{
  var p := step.p; // syntax
  var take := step.take;
  && p < |v.piles|
  && take <= v.piles[p]
  && v'.piles == v.piles[p := v.piles[p] - take]
}

// nearly boilerplate (just gather up all transitions)
ghost predicate NextStep(v: Variables,  v': Variables, step: Step) {
  match step {
    case TurnStep(_, _) => Turn(v, v', step)
  }
}

// boilerplate - always the same
lemma NextStepDeterminsticGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
{
}

// boilerplate - always the same
ghost predicate Next(v: Variables,  v': Variables) {
  exists step :: NextStep(v, v', step)
}
