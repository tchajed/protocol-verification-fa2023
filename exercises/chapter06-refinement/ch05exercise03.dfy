// Two Phase Commit Safety Proof
// Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "ch05exercise02.dfy"

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the decision at the coordinator
  ghost predicate DecisionMsgsAgreeWithCoordinator(v: Variables)
    requires v.WF()
  {
    // SOLUTION
    forall msg |
      && msg in v.network.sentMsgs
      && msg.DecisionMsg?
      :: CoordinatorVars(v).decision == Some(msg.decision)
         // END
  }

  // We use this block of code to define additional invariants. We recommend you
  // define predicates for the individual parts of your invariant, to make
  // debugging easier.
  // SOLUTION
  ghost predicate VoteMessagesAgreeWithParticipantPreferences(v: Variables)
    requires v.WF()
  {
    (forall msg |
       && msg in v.network.sentMsgs
       && msg.VoteMsg?
       && ValidParticipantId(v, msg.sender)
       :: msg.vote == ParticipantVars(v, msg.sender).c.preference
    )
  }

  ghost predicate CoordinatorStateSupportedByVote(v: Variables)
    requires v.WF()
  {
    (forall idx:HostId |
       && ValidParticipantId(v, idx)
       && CoordinatorVars(v).votes[idx].Some?
       :: VoteMsg(idx, CoordinatorVars(v).votes[idx].value) in v.network.sentMsgs
    )
  }

  ghost predicate CoordinatorDecisionReflectsPreferences(v: Variables)
    requires v.WF()
  {
    CoordinatorVars(v).decision.Some? ==>
      && var d := CoordinatorVars(v).decision.value;
      && d == (if (forall h | ValidParticipantId(v, h) :: ParticipantVars(v, h).c.preference.Yes?) then Commit else Abort)
  }
  // END


  ghost predicate Inv(v: Variables)
  {
    && v.WF()
       // SOLUTION
    && VoteMessagesAgreeWithParticipantPreferences(v)
    && CoordinatorStateSupportedByVote(v)
    && CoordinatorDecisionReflectsPreferences(v)
       // END
       // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithCoordinator(v)
       // ...but you'll need more.
    && Safety(v)
  }

  lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    // SOLUTION
    // END
  }

  lemma InvInductive(v: Variables, v': Variables, event: Event)
    requires Inv(v)
    requires Next(v, v', event)
    ensures Inv(v')
  {
    // SOLUTION
    var step :| NextStep(v, v', event, step);
    assert step.HostActionStep?;
    var hostId := step.hostId;
    var msgOps := step.msgOps;
    if v.hosts[hostId].CoordinatorVariables? {
      // coordinator proof
      assert hostId == |v.hosts| - 1; // this is the coordinator
      assert forall hostId':HostId | ValidParticipantId(v, hostId') ::
          ParticipantVars(v', hostId') == ParticipantVars(v, hostId');
      var cstep :| CoordinatorHost.NextStep(CoordinatorVars(v), CoordinatorVars(v'), cstep, msgOps, event);
      match cstep {
        case SendReqStep => { return; }
        case LearnVoteStep => { return; }
        case DecideStep(decision) => { return; }
      }
    } else {
      // participant proof
      assert v.hosts[hostId].ParticipantVariables?;
      var pstep :| ParticipantHost.NextStep(ParticipantVars(v, hostId), ParticipantVars(v', hostId), pstep, msgOps, event);
      assert ParticipantVars(v', hostId).c == ParticipantVars(v, hostId).c;
      assert forall hostId':HostId | ValidParticipantId(v, hostId') && hostId' != hostId
          :: ParticipantVars(v', hostId') == ParticipantVars(v, hostId');
      match pstep {
        case VoteStep => {
          assert CoordinatorVars(v') == CoordinatorVars(v);
          assert CoordinatorStateSupportedByVote(v');
          if ParticipantVars(v, hostId).c.preference.No? {
            return;
          }
          assert ParticipantVars(v', hostId) == ParticipantVars(v, hostId);
          assert SafetyAC1(v');
          assert SafetyAC3(v');
          assert SafetyAC4(v');
          return;
        }
        case LearnDecisionStep => { return; }
      }
    }
    // END
  }

  lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
