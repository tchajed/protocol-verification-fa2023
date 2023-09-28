// Nim version 3: demonstrate a behavior

datatype Player = P1 | P2
{
  function Other(): Player {
    if this == P1 then P2 else P1
  }
}
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
  && v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
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

lemma ExampleBehavior() returns (b: seq<Variables>)
  ensures |b| > 0
  ensures Init(b[0])
  ensures forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1])
{
  var state0 := Variables(piles := [3, 5, 7], turn := P1); // syntax
  b := [
    state0,
    Variables(piles := [3, 1, 7], turn := P2),
    Variables(piles := [3, 1, 0], turn := P1)
  ];
  assert NextStep(b[0], b[1], TurnStep(take := 4, p := 1));
  assert NextStep(b[1], b[2], TurnStep(take := 7, p := 2));
}
