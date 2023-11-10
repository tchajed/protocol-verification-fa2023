// Property Lemmas for Atomic Commit
// The state machine model captures AC2 nicely,
// but let's make it very clear that the model also obeys
// AC1, AC3 and AC4.

// To increase our confidence that our state machine spec from
// exercise02 accurately defines our goal, we can state and prove some
// properties about it. These are above and on top of refinement.
//
// AC1: All processes that reach a decision reach the same one.
// AC3: The Commit decision can only be reached if all processes prefer Yes.
// AC4: If all processes prefer Yes, then the decision must be Commit.
//
// AC2: (stability) A process cannot reverse its decision after it has reached one.
// We'll not bother with AC2 because it can't be stated as a safety
// property, however it should be abundantly clear from the Next
// action of the state machine model.
//
// AC5: (liveness) All processes eventually decide.
// We'll not bother with AC5 because it's a liveness property, which
// is outside the scope of this course.
//
// If you wrote a broken spec in exercise01, it will be difficult to prove these
// properties on it (and probably also difficult to prove refinement).

include "exercise01.dfy"

module AtomicCommitProperties {
  import opened CommitTypes
  import opened AtomicCommit

  ghost predicate SafetyAC1(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 4 lines)
    false // Replace me
    // END EDIT
  }

  // AC2 can't be stated about a single state; the "code reviewer"
  // should be able to confirm it by reading the state machine spec
  // from exercise02.

  ghost predicate SafetyAC3(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 6 lines)
    false // Replace me
    // END EDIT
  }

  ghost predicate SafetyAC4(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 4 lines)
    false // Replace me
    // END EDIT
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  ghost predicate Safety(v: Variables)
  {
    && v.WF()
    && SafetyAC1(v)
    && SafetyAC3(v)
    && SafetyAC4(v)
  }

  lemma SafetyInit(v: Variables)
    requires Init(v)
    ensures Safety(v)
  {
  }

  lemma SafetyNext(v: Variables, v': Variables, event: Event)
    requires Safety(v)
    requires Next(v, v', event)
    ensures Safety(v')
  {
  }
}
