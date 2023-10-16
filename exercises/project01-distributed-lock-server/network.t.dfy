// Network
// This file has no editable regions because it's a trusted file that specifies
// how the network delivers packets, allowing reorder and duplicate delivery.

include "UtilitiesLibrary.dfy"

module HostIdentifiers {
  type HostId = int // Pretty type synonym (a la C typedef)

  ghost predicate ValidHostId(numHosts: nat, hostid: HostId) {
    0 <= hostid < numHosts
  }

  // The set of all host identities.
  ghost function AllHosts(numHosts: nat) : set<HostId> {
    set hostid:HostId |
    && 0 <= hostid < numHosts // This line is entirely redundant, but it satisfies Dafny's finite-set heuristic
    && ValidHostId(numHosts, hostid)
  }
}

// This version of Network uses a template parameter to avoid having to declare
// the Message type before the Network module. (Contrast with ch05/ex02.)
module Network {
  import opened UtilitiesLibrary

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps<Message> = MessageOps(recv:Option<Message>, send:Option<Message>)

  datatype Constants = Constants(numHosts: nat)

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables<Message> = Variables(c: Constants, sentMsgs:set<Message>)

  ghost predicate Init<Message>(v: Variables<Message>)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next<Message>(v: Variables<Message>, v': Variables<Message>,
                                msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    && v'.c == v.c
       // Record the sent message, if there was one.
    && v'.sentMsgs ==
       v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }

  lemma NextStepDeterministic(v: Variables,
                              v'1: Variables, v'2: Variables,
                              msgOps: MessageOps)
    requires Next(v, v'1, msgOps)
    requires Next(v, v'2, msgOps)
    ensures v'1 == v'2
  {}
}
