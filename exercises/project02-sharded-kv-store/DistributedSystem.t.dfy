include "Network.t.dfy"
include "Host.v.dfy"

// Everything in this file is standard: we combine instantiate the host model
// for a whole sequence of hosts, and combine it the network.

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  type HostId = Network.HostId

  datatype Variables = Variables(hosts: seq<Host.Variables>, network: Network.Variables)
  {
    ghost predicate ValidHost(idx: HostId) {
      idx < |hosts|
    }

    ghost predicate WF() {
      && 0 < |hosts|
      && forall idx: HostId | ValidHost(idx) :: hosts[idx].GroupWF(idx)
    }
  }

  ghost predicate Init(v: Variables)
  {
    && v.WF()
    && (forall idx: HostId | v.ValidHost(idx) :: Host.Init(v.hosts[idx]))
    && Network.Init(v.network)
  }

  ghost predicate OtherHostsUnchanged(v: Variables, v': Variables, hostId: HostId)
    requires v.WF() && v'.WF()
    requires |v.hosts| == |v'.hosts|
    requires v.ValidHost(hostId)
  {
    forall otherId: HostId | v.ValidHost(otherId) && hostId != otherId ::
      v'.hosts[otherId] == v.hosts[otherId]
  }

  datatype Step =
    | HostStep(msgOps: Network.MessageOps, hostId: HostId)

  ghost predicate NextStep(v: Variables, v': Variables, event: Event, step: Step)
  {
    && v.WF()
    && v'.WF()
    && step.HostStep?
    && var hostId := step.hostId;
    && var msgOps := step.msgOps;
    && v.ValidHost(hostId)
    && |v'.hosts| == |v.hosts| // this is constant
    && Host.Next(v.hosts[hostId], v'.hosts[hostId], msgOps, event)
    && Network.Next(v.network, v'.network, msgOps)
    && OtherHostsUnchanged(v, v', hostId)
  }

  ghost predicate Next(v: Variables, v': Variables, event: Event)
  {
    && exists step: Step :: NextStep(v, v', event, step)
  }
}
