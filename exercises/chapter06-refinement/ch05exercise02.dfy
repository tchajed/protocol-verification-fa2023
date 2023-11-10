// Two Phase Commit Safety Specification Predicate
// Express the English Atomic Commit safety properties as predicates
// over the compound state machine model from exercise01.

// 2PC should satisfy the Atomic Commit specification. English design doc:
//
// AC-1: All processes that reach a decision reach the same one.
// AC-3: If any host has a No preference, then the decision must be Abort.
// AC-4: If all processes prefer Yes, then the decision must be Commit.
//
// Note that the full Atomic Commit spec includes these additional properties,
// but you should ignore them for this exercise:
// AC-2: (stability) A process cannot reverse its decision after it has reached one.
//       (best modeled with refinement)
// AC-5: (liveness) All processes eventually decide.

// Note that this specification depends on your model from exercise 1, so you
// should write your spec accordingly. Of course, that also means
// double-checking that your model performs all actions as described.
include "ch05exercise01.dfy"

module Obligations {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
    // Here are some handy accessor functions for dereferencing the coordinator
    // and the participants out of the sequence in Hosts.
  ghost function CoordinatorVars(v: Variables) : CoordinatorHost.Variables
    requires v.WF()
  {
    Last(v.hosts).coordinator
  }

  ghost predicate ValidParticipantId(v: Variables, hostid: HostId)
  {
    hostid < |v.hosts|-1
  }

  ghost function ParticipantVars(v: Variables, hostid: HostId) : ParticipantHost.Variables
    requires v.WF()
    requires ValidParticipantId(v, hostid)
  {
    v.hosts[hostid].participant
  }

  // AC-1: All processes that reach a decision reach the same one.
  ghost predicate SafetyAC1(v: Variables)
    requires v.WF()
  {
    // All hosts that reach a decision reach the same one
    // SOLUTION
    // HAND-GRADE
    // All hosts that reach a decision reach the same one
    forall h1, h2 | ValidParticipantId(v, h1) && ValidParticipantId(v, h2) ::
      ParticipantVars(v, h1).decision.Some? && ParticipantVars(v, h2).decision.Some? ==>
        ParticipantVars(v, h1).decision.value == ParticipantVars(v, h2).decision.value
      // END
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: If any host has a No preference, then the decision must be Abort.
  ghost predicate SafetyAC3(v: Variables)
    requires v.WF()
  {
    // SOLUTION
    // HAND-GRADE
    // Any host with a No preference forces an abort.
    (exists hostid:HostId ::
       && ValidParticipantId(v, hostid)
       && ParticipantVars(v, hostid).c.preference.No?)
    ==> forall h:HostId | ValidParticipantId(v, h) && ParticipantVars(v, h).decision.Some? ::
        ParticipantVars(v, h).decision.value == Abort
    // END
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(v: Variables)
    requires v.WF()
  {
    // SOLUTION
    // HAND-GRADE
    // If every host has a Yes preference we must commit.
    (forall hostid:HostId | ValidParticipantId(v, hostid) ::
       ParticipantVars(v, hostid).c.preference.Yes?)
    ==> forall h:HostId | ValidParticipantId(v, h) && ParticipantVars(v, h).decision.Some? ::
        ParticipantVars(v, h).decision.value == Commit
    // END
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  ghost predicate Safety(v: Variables)
    requires v.WF()
  {
    && SafetyAC1(v)
    && SafetyAC3(v)
    && SafetyAC4(v)
  }
}
