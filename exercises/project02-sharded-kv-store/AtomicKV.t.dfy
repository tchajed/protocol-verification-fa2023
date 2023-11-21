include "IMapHelpers.t.dfy"
include "Types.t.dfy"

// The application spec for this system is a key-value store
// that maintains a map of int keys to int values. This file is trusted and
// doesn't have any holes for you to fill in, but you should read it since it
// describes what your protocol is intended to do.
//
// The type of the state in this state machine is simply a total imap: one in
// which every possible key is in the domain. (Unlike in the chapter06 demo,
// this is an imap and permits an infinite keyspace, so we won't need to reason
// about the union of domains.)
//
// The user-visible actions are Get and Put operations.
// - Get accepts a key and returns a value.
// - Put accepts a key and a value and returns nothing (acknowledging completion).
//
// As in chapter06, we use refinement to specify the expected behavior with an
// atomic state machine -- one that consumes an input and delivers an output in
// a single transition. We do make one small tweak and actually use NoOpEvent
// for the no-op steps, rather than putting them in the refinement obligation.

module AtomicKV {
  import opened IMapHelpers
  import opened Types

  datatype Variables = Variables(table: imap<int, int>)

  // The initial map should assign the value zero to every key.
  ghost predicate Init(v: Variables) {
    && v.table == ZeroMap()
  }

  ghost predicate Get(v: Variables, v': Variables, key: int, value: int) {
    && v' == v
    && key in v.table
    && value == v.table[key]
  }

  ghost predicate Put(v: Variables, v': Variables, key: int, value: int) {
    && key in v.table
    && v'.table == v.table[key := value]
  }

  ghost predicate NoOp(v: Variables, v': Variables) {
    && v' == v
  }

  ghost predicate Next(v: Variables, v': Variables, event: Event) {
    match event {
      case GetEvent(key, value) => Get(v, v', key, value)
      case PutEvent(key, value) => Put(v, v', key, value)
      case NoOpEvent() => NoOp(v, v')
    }
  }
}
