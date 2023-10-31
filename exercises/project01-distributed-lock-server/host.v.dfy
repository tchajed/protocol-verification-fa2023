// Host protocol
// Define the host state machine here: message type, state machine for executing one
// host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
    // FIXME: fill in here (solution: 1 line)
     Message() // Populate this datatype.
    // END EDIT

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId)

  datatype Variables = Variables(
    // FIXME: fill in here (solution: 2 lines)
     c: Constants
    // Fill me in.
    // END EDIT
  )

  // You can assume in Init below that the initial constants are set by the
  // DistributedSystem composite state machine, since we assume the host state
  // machine knows the correct total number of hosts and its own ID.

  ghost predicate Init(v:Variables) {
    // FIXME: fill in here (solution: 2 lines)
        true // Replace me
    // END EDIT
  }
  // FIXME: fill in here (solution: 22 lines)
  // END EDIT
  // JayNF
  datatype Step =
      // FIXME: fill in here (solution: 2 lines)
     | SomeStep   // Replace me
      // END EDIT

  ghost predicate NextStep(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    && v'.c == v.c
    && match step
       // FIXME: fill in here (solution: 2 lines)
        case SomeStep => true
       // END EDIT
  }

  lemma NextStepDeterministic(v: Variables, v'1: Variables, v'2: Variables, msgOps: Network.MessageOps<Message>, step: Step)
    requires NextStep(v, v'1, msgOps, step)
    requires NextStep(v, v'2, msgOps, step)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(v, v', msgOps, step)
  }
}
