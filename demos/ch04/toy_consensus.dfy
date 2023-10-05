// Ported from ivy/examples/ivy/toy_consensus.ivy.

type Node(==)
type Quorum(==)
type Choice(==)

predicate Member(n: Node, q: Quorum)

// axiom: any two quorums intersect in at least one node
lemma QuorumIntersect(q1: Quorum, q2: Quorum) returns (n: Node)
  ensures Member(n, q1) && Member(n, q2)

datatype Variables = Variables(
  votes: map<Node, set<Choice>>,
  decision: set<Choice>
)
{
  ghost predicate WF()
  {
    && (forall n:Node :: n in votes)
  }
}

datatype Step =
  | CastVoteStep(n: Node, c: Choice)
  | DecideStep(c: Choice, q: Quorum)

ghost predicate CastVote(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.CastVoteStep?
{
  var n := step.n;
  && (v.votes[n] == {})
  && (v' == v.(votes := v.votes[n := v.votes[n] + {step.c}]))
}

ghost predicate Decide(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.DecideStep?
{
  // if all nodes of a quorum have voted for a value, then that value can be a
  // decision
  && (forall n: Node | Member(n, step.q) :: step.c in v.votes[n])
  && v' == v.(decision := v.decision + {step.c})
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  && v.WF()
  && match step {
       case CastVoteStep(_, _) => CastVote(v, v', step)
       case DecideStep(_, _) => Decide(v, v', step)
     }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

ghost predicate Init(v: Variables) {
  && v.WF()
  && (forall n :: v.votes[n] == {})
  && v.decision == {}
}

ghost predicate Safety(v: Variables) {
  forall c1, c2 :: c1 in v.decision && c2 in v.decision ==> c1 == c2
}

// this definition is left in as a hint towards writing the invariant
ghost predicate ChoiceQuorum(v: Variables, q: Quorum, c: Choice)
  requires v.WF()
{
  forall n :: Member(n, q) ==> c in v.votes[n]
}

ghost predicate Inv(v: Variables) {
  && v.WF()
  && Safety(v)
     // we will need to strengthen the invariant
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{
}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  match step {
    case CastVoteStep(n, c) => {
      return;
    }
    case DecideStep(c, q) => {
      return;
    }
  }
}

lemma SafetyHolds(v: Variables, v': Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  if Inv(v) && Next(v, v') {
    InvInductive(v, v');
  }
}
