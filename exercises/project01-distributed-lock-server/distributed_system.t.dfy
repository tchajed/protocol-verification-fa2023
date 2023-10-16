// DistributedSystem
// This file isn't editable because it's a trusted file that specifies how
// hosts interact with one another over the network.

include "host.v.dfy"

// Before we get here, caller must define a type Message that we'll
// use to instantiate network.v.dfy.

module DistributedSystem {
  import opened HostIdentifiers
  import Host
  import Network

  datatype Variables = Variables(
    hosts:seq<Host.Variables>,
    network:Network.Variables<Host.Message>) {

    ghost predicate ValidHostId(id: HostId) {
      HostIdentifiers.ValidHostId(|hosts|, id)
    }

    ghost predicate WF() {
      // host and network constants have the correct parameters from the global
      // distributed system
      && (forall id | ValidHostId(id) ::
            // every host knows its id (and ids are unique)
            && hosts[id].c.numHosts == |hosts|
            && hosts[id].c.myId == id)
      && network.c.numHosts == |hosts|
    }
  }

  ghost predicate Init(v:Variables) {
    && v.WF()
    && (forall id | v.ValidHostId(id) :: Host.Init(v.hosts[id]))
    && Network.Init(v.network)
  }

  // JayNF
  datatype Step = Step(id:HostId, msgOps: Network.MessageOps<Host.Message>)

  ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
    && v.WF()
    && v.ValidHostId(step.id)
    && |v'.hosts| == |v.hosts|
    && Host.Next(v.hosts[step.id], v'.hosts[step.id], step.msgOps)
    && (forall other | v.ValidHostId(other) && other != step.id :: v'.hosts[other] == v.hosts[other])
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(v:Variables, v':Variables) {
    exists step :: NextStep(v, v', step)
  }
}
