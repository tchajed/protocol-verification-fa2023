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
    //#solution
    Grant(dest:HostId, epoch:nat)
    //#stub
    // Message() // Populate this datatype.
    //#end

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId)

  datatype Variables = Variables(
    //#solution
    c: Constants,
    holdsLock:bool, epoch:nat
    //#stub
    // c: Constants
    //// Fill me in.
    //#end
  )

  // You can assume in Init below that the initial constants are set by the
  // DistributedSystem composite state machine, since we assume the host state
  // machine knows the correct total number of hosts and its own ID.

  ghost predicate Init(v:Variables) {
    //#solution
    && v.holdsLock == (v.c.myId == 0)
    && v.epoch == if v.c.myId == 0 then 1 else 0
       //#stub
       // true // Replace me
       //#end
  }
  //#solution
  ghost predicate DoGrant(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step)
    requires step.DoGrantStep?
  {
    var recipient := step.recipient;
    && v.holdsLock == true
    && msgOps.recv.None?
    && ValidHostId(v.c.numHosts, recipient) // Doesn't actually affect safety, but does affect liveness! if we grant to msgOps nonexistent host, no further steps will occur.
    && msgOps.send == Some(Grant(recipient, v.epoch + 1))
    && v'.holdsLock == false
    && v'.epoch == v.epoch
  }

  ghost predicate DoAccept(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step)
    requires step.DoAcceptStep?
  {
    && msgOps.recv.Some?
    && msgOps.recv.value.dest == v.c.myId
    && msgOps.recv.value.epoch > v.epoch
    && msgOps.send == None
    && v'.epoch == msgOps.recv.value.epoch
    && v'.holdsLock == true
  }
  //#stub
  //#end
  // JayNF
  datatype Step =
      //#solution
    | DoGrantStep(recipient: HostId)
    | DoAcceptStep
      //#stub
    // | SomeStep   // Replace me
    //#end

  ghost predicate NextStep(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    && v'.c == v.c
    && match step
       //#solution
       case DoGrantStep(_) => DoGrant(v, v', msgOps, step)
       case DoAcceptStep => DoAccept(v, v', msgOps, step)
       //#stub
       // case SomeStep => true
       //#end
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
