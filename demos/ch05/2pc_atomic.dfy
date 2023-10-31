// A synchronous model of two-phase commit, without a network between hosts.

datatype Option<T> = Some(value: T) | None

datatype Vote = Yes | No
datatype Decision = Commit | Abort

datatype Participant = Participant(pref: Vote, decision: Option<Decision>)
datatype Coordinator = Coordinator(prefs: seq<Option<Vote>>, decision: Option<Decision>)

datatype Variables = Variables(participants: seq<Participant>, coordinator: Coordinator)
{
  ghost predicate WF() {
    |coordinator.prefs| == |participants|
  }

  ghost predicate ValidId(i: int) {
    0 <= i < |participants|
  }
}

ghost predicate Init(v: Variables) {
  && v.WF()
  && (forall i | v.ValidId(i) :: v.participants[i].decision.None?) // pref is arbitrary
  && (forall i | v.ValidId(i) :: v.coordinator.prefs[i] == None)
  && v.coordinator.decision == None
}

datatype Step =
    /* | VoteReq */ // instead of a VoteReq step, participants can always send pref
  | VoteRespStep(i: nat) // one participant sends its pref to coordinator
  | CoordDecideStep // coordinator decides when it has all prefs
  | DecisionAnnounceStep(i: nat, decision: Decision) // coordinator tells one participant the outcome

ghost predicate VoteResp(v: Variables, v': Variables, step: Step)
  requires step.VoteRespStep?
{
  && v.WF()
  && v.ValidId(step.i)
  && var pref := v.participants[step.i].pref;
  && v'.coordinator.prefs == v.coordinator.prefs[step.i := Some(pref)]
  && v'.coordinator.decision == v.coordinator.decision
  && v'.participants == v.participants
}

ghost predicate CoordinatorDecide(v: Variables, v': Variables, step: Step)
  requires step.CoordDecideStep?
{
  && v.WF()
  && (forall i | v.ValidId(i) :: v.coordinator.prefs[i].Some?)
  && v'.coordinator.prefs == v.coordinator.prefs
  && v'.coordinator.decision ==
     Some(if (forall i | v.ValidId(i) :: v.coordinator.prefs[i].value == Yes) then Commit else Abort)
  && v'.participants == v.participants
}

ghost predicate DecisionAnnounce(v: Variables, v': Variables, step: Step)
  requires step.DecisionAnnounceStep?
{
  && v.WF()
  && var i := step.i;
  && v.ValidId(i)
  && v.coordinator.decision.Some?
  && v.coordinator.decision.value == step.decision
  && v'.coordinator == v.coordinator
  && v'.participants == v.participants[i := v.participants[i].(decision := Some(step.decision))]
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case VoteRespStep(i) => VoteResp(v, v', step)
    case CoordDecideStep => CoordinatorDecide(v, v', step)
    case DecisionAnnounceStep(i, decision) => DecisionAnnounce(v, v', step)
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, v'1: Variables, v'2: Variables, step: Step)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  requires v'1 == v'2
{}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

// participants reach consensus (at most one decision)
ghost predicate Consensus(v: Variables)
  requires v.WF()
{
  forall i, j | v.ValidId(i) && v.ValidId(j) ::
    v.participants[i].decision.Some? && v.participants[j].decision.Some? ==>
      v.participants[i].decision.value == v.participants[j].decision.value
}

// must reach commit if all participants vote yes
ghost predicate CommitSafe(v: Variables)
  requires v.WF()
{
  // FIXME: fill in here (solution: 3 lines)
  true
  // END EDIT
}

// must reach abort if any participant votes no
ghost predicate AbortSafe(v: Variables)
  requires v.WF()
{
  // FIXME: fill in here (solution: 3 lines)
  true
  // END EDIT
}

ghost predicate Safety(v: Variables)
{
  && v.WF()
  && Consensus(v)
  && CommitSafe(v)
  && AbortSafe(v)
}

// Define your inductive invariant here.

// FIXME: fill in here (solution: 34 lines)
// END EDIT

ghost predicate Inv(v: Variables)
{
  // FIXME: fill in here (solution: 5 lines)
  && Safety(v)
  // END EDIT
}

lemma InvInit(v: Variables)
  requires Init(v)
  ensures Inv(v)
{}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v) && Next(v, v')
  ensures Inv(v')
{
  // FIXME: fill in here (solution: 17 lines)
  var step :| NextStep(v, v', step);
  match step {
    case VoteRespStep(i) => {
      return;
    }
    case CoordDecideStep => {
      return;
    }
    case DecisionAnnounceStep(i, decision) => {
      return;
    }
  }
  // END EDIT
}

lemma InvSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{
}

lemma SafetyAlwaysHolds(v: Variables, v': Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  if Init(v) { InvInit(v); }
  if Inv(v) && Next(v, v') { InvInductive(v, v'); }
  if Inv(v) { InvSafety(v); }
}
