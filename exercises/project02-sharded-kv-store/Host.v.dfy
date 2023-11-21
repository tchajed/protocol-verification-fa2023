include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
include "MessageType.v.dfy"
include "Network.t.dfy"

// You'll need protocol steps for Get and Put that respond to requests if
// they're hosted locally, much like in the atomic version of this protocol
// (AtomicKV, seen in the chapter06 demos). These need to set the event to
// GetEvent and PutEvent appropriately: otherwise, you're claiming the key-value
// store implementation always does nothing and never returns results to the
// client. (Such an implementation is technically safe but totally useless and
// not in the spirit of the assignment; to be clear, it's not a real solution.)
//
// In addition, you should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKV, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

  datatype Variables = Variables(myId: HostId, m: imap<int, int>)
  {
    ghost predicate GroupWF(assignedId: HostId) {
      && this.myId == assignedId
    }
  }

  ghost predicate Init(v: Variables) {
    // hint: look at IMapHelpers for some tools to write this
    // FIXME: fill in here (solution: 2 lines)
    && true
    // END EDIT
  }

  datatype Step =
      // FIXME: fill in here (solution: 4 lines)
    | ProtocolStepsHere // Replace me
      // END EDIT

  // Write a predicate for each step here.
  // FIXME: fill in here (solution: 53 lines)
  // END EDIT

  ghost predicate NextStep(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event, step: Step)
  {
    match step {
      // boilerplate that dispatches to each of your step's predicates
      // FIXME: fill in here (solution: 4 lines)
      case ProtocolStepsHere => true
      // END EDIT
    }
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
  {
    exists step: Step :: NextStep(v, v', msgOps, event, step)
  }
}
