# 2PC refinement

The files ch05exercise01.dfy, ch05exercise02.dfy, and ch05exercise03.dfy are an
instructor-provided solution to ch5, with some tweaks to the state machine
definition to make it suitable for refinement. In particular, we've gone through
the host and distributed system state machines and added an "event" parameter to
all the Next and transition predicates that will be used in the chapter 6
refinement theorems.

Each transition now specifies which "event" it is simulating from a more
abstract state machine that models two-phase commit. You'll define exactly what
those events mean when you define that abstract state machine in exercise01, and
in the refinement proof (exercise03) you'll show that when the distributed state
machine claims that `event` happened the abstract state machine agrees.

The exact events the distributed state machine "emits" (alongside each
transition) will probably make more sense when you get to doing the refinement
proof; at that point we'd recommend coming back and reading these definitions.
You'll notice many steps prove the abstract state doesn't change and use the
NoOpEvent. This is because even though the distributed state machine
transitioned and made progress, it's claiming to have made no progress in the
_abstract_ state machine. For example, sending votes to the coordinator doesn't
actually change any decisions; our abstract state machine only considers
participant decisions to be events.
