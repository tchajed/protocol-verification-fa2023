// Sharded KV store with atomic, synchronous communication
// A refinement from a protocol (distributed sharded state) to
// a specification (a logically-centralized abstract map).

// In this system model, communication is synchronous and atomic. Network
// messages are delivered instantaneously -- this keeps things simpler but is
// clearly an unrealistic assumption for a real system.

include "UtilitiesLibrary.dfy"

module Types {
  // Rather than concretely explain the Key and Value types, we define the spec
  // and protocol over some uninterpreted types. The type declaration below says "there
  // is some type Key, but this protocol's behavior doesn't depend on what actual
  // type it is."

  // We need to tell Dafny two things about the type to convince it the type behaves
  // mathematically:
  // (==) means whatever this type is, it has equality defined on it.
  // !new means this type can't be allocated on the heap; it's a mathematical
  // immutable object.
  // Since we're in math-land, not implementation-land, we always want both features
  // of all types, so we declare them on these otherwise-unspecified types.
  // Missing == gives "map domain type must support equality" errors.
  // Missing !new gives "...not allowed to depend on the set of allocated
  // references" errors.
  type Key(==, !new)

  // Dafny's map<> type requires a finite domain. It also has an imap<> type that
  // allows an infinite domain, but we'd like to defer that complexity, so we'll stick
  // with finite maps.
  // Looking forward to the implementation, we can start with no keys stored, but we
  // are going to need to store "shard authority" information (which host is responsible
  // for each key) for every possible key, so eventually we're going to need to
  // have maps that contain every possible key. If we want to avoid imap<> for now,
  // then we'll need a finite keyspace. `type Key` is uninterpreted, and there's
  // no easy way to declare that it's finite.
  // (Side note: actually there is; Dafny has a predicate type constructor, but it's
  // flaky and sometimes crashes Dafny, so we're going to steer clear of it, too.)

  // So, just as we assume there's some space of Keys, let's assume a function that
  // defines a finite subset of those keys as the keyspace we're actually going to use.
  // We leave the function body absent, which means it's an axiom: we don't provide
  // the function, but assume such a function exists.
  // Everywhere we use a Key, we'll also require it to be in AllKeys().
  ghost function AllKeys() : set<Key>

  type Value(==, 0, !new)

  // To keep the API simple, we omit the concept of "the absence of a key", and instead
  // assume a DefaultValue that keys have until Inserted otherwise.
  ghost const DefaultValue : Value

  // This map comprehension assigns the DefaultValue to every key in the finite AllKeys()
  // keyspace. (Note that here the finite-ness of AllKeys() is now essential, as
  // it shows Dafny than the map has finite domain.)
  ghost function InitialMap() : map<Key, Value>
  {
    map key | key in AllKeys() :: DefaultValue
  }

  datatype Event =
    | GetEvent(key: Key, value: Value)
    | PutEvent(key: Key, value: Value)
    | NoOpEvent()
}

// This module defines a Map state machine that serves as the system specification.
// You can tell by looking at this state machine that Key-Value pairs that get inserted
// are returned in Queries until otherwise inserted. It only talks about the semantics
// of Insert and Query; all of the details of a sharded implementation are left to
// the implementation.
module MapSpec {
  import opened Types

  datatype Variables = Variables(mapp:map<Key, Value>)

  ghost predicate Init(v: Variables)
  {
    v.mapp == InitialMap()
    // Initially, every key maps to DefaultValue.
  }

  ghost predicate Get(v:Variables, v':Variables, key:Key, output:Value)
  {
    && key in AllKeys()
              // This is always true, but only visible by an inductive proof. We assume
              // it here so we can dereference v.mapp[key] on the next line. (If my claim
              // were wrong, then some Querys would be rejected by this test, which is a
              // liveness failure but not a safety failure.)
    && key in v.mapp
    && output == v.mapp[key]
    && v' == v  // no change to map state
  }

  ghost predicate Put(v:Variables, v':Variables, key:Key, value:Value)
  {
    // A well-formed condition: we're not even gonna talk about keys other than AllKeys().
    && key in AllKeys()
              // Replace key with value. v.mapp domain remains AllKeys().
    && v'.mapp == v.mapp[key := value]
  }

  ghost predicate NoOp(v:Variables, v':Variables)
  {
    && v' == v
  }

  ghost predicate Next(v: Variables, v': Variables, event: Event)
  {
    match event {
      case GetEvent(key, value) => Get(v, v', key, value)
      case PutEvent(key, value) => Put(v, v', key, value)
      case NoOpEvent() => NoOp(v, v')
    }
  }
}

module ShardedKVProtocol {
  import opened Types
  import opened UtilitiesLibrary

  type HostIdx = nat

  datatype Variables = Variables(maps:seq<map<Key, Value>>)
  {
    function mapCount(): nat {
      |maps|
    }

    ghost predicate WF() {
      && mapCount() > 0
    }

    ghost predicate ValidHost(idx: HostIdx) { idx < mapCount() }
  }

  ghost predicate Init(v: Variables)
  {
    && v.WF()
    && (forall idx:HostIdx | v.ValidHost(idx) :: v.maps[idx] == if idx==0 then InitialMap() else map[])
  }

  ghost predicate Insert(v: Variables, v': Variables, event: Event, idx: HostIdx, key: Key, value: Value)
  {
    && event == PutEvent(key, value)
    && v.WF()
    && v.ValidHost(idx)
    && v'.mapCount() == v.mapCount()
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
              //&& key in AllKeys() // implied by previous conjunct + Inv()ariant
    && v'.maps == v.maps[idx := v.maps[idx][key := value]]
  }

  ghost predicate Query(v: Variables, v': Variables, event: Event, idx: HostIdx, key: Key, output: Value)
  {
    && event == GetEvent(key, output)
    && v.WF()
    && v.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    && output == v.maps[idx][key]
    && v' == v  // UNCHANGED
  }

  // A possible enhancement exercise: transfer many key,value pairs in one step
  ghost predicate Transfer(v: Variables, v': Variables, event: Event, sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)
  {
    && event == NoOpEvent()
    && v.WF()
    && v'.WF()
    && v.ValidHost(sendIdx)
    && v.ValidHost(recvIdx)
    && v'.mapCount() == v.mapCount()
    && key in v.maps[sendIdx]
    && v.maps[sendIdx][key] == value
    && v'.maps[sendIdx] == MapRemoveOne(v.maps[sendIdx], key)  // key leaves sending map
    && v'.maps[recvIdx] == v.maps[recvIdx][key := value]    // key appears in recv map
    && (forall otherIdx:HostIdx | v.ValidHost(otherIdx) && otherIdx != sendIdx && otherIdx != recvIdx
          :: v'.maps[otherIdx] == v.maps[otherIdx]) // unchanged other participants
  }

  datatype Step =
    | InsertStep(idx: HostIdx, key: Key, value: Value)
    | QueryStep(idx: HostIdx, key: Key, output: Value)
    | TransferStep(sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)

  ghost predicate NextStep(v: Variables, v': Variables, event: Event, step: Step)
  {
    match step
    case InsertStep(idx, key, value) => Insert(v, v', event, idx, key, value)
    case QueryStep(idx, key, output) => Query(v, v', event, idx, key, output)
    case TransferStep(sendIdx, recvIdx, key, value) => Transfer(v, v', event, sendIdx, recvIdx, key, value)
  }

  ghost predicate Next(v: Variables, v': Variables, event: Event)
  {
    exists step :: NextStep(v, v', event, step)
  }
}

module RefinementProof {
  import opened Types
  import opened UtilitiesLibrary
  import MapSpec
  import opened ShardedKVProtocol

  ghost predicate HostHasKey(v: Variables, hostidx:HostIdx, key:Key)
    requires v.WF()
  {
    && v.ValidHost(hostidx)
    && key in v.maps[hostidx]
  }

  // Pulling the choose out into its own function is often necessary due to how
  // its implemented in Dafny.
  ghost function KeyHolder(v: Variables, key:Key) : HostIdx
    requires v.WF()
    requires exists hostidx :: HostHasKey(v, hostidx, key)
  {
    var hostidx:HostIdx :| HostHasKey(v, hostidx, key);
    hostidx
  }


  ghost function AbstractionOneKey(v: Variables, key:Key) : Value
    requires v.WF()
  {
    // DONE: fill in here (solution: 4 lines)
    if exists hostidx :: HostHasKey(v, hostidx, key) then
      var hostidx := KeyHolder(v, key);
      v.maps[hostidx][key]
    else
      DefaultValue
      // END EDIT
  }

  // We construct the finite set of possible map keys here, all
  // because we need to supply Dafny with simple evidence that our map domain
  // is finite for the map comprehension in Abstraction().
  // (An alternative would be to switch to imaps -- maps with potentially-infinite
  // domains -- but that would require making the spec fancier. This was a compromise.)

  // The sequence of map domains. Pulled out into its own function to
  // make proof assertions easy to write.
  ghost function MapDomains(v: Variables) : seq<set<Key>>
    requires v.WF()
  {
    seq(v.mapCount(), i requires 0<=i<v.mapCount() => v.maps[i].Keys)
  }

  ghost function KnownKeys(v: Variables) : set<Key>
    requires v.WF()
  {
    UnionSeqOfSets(MapDomains(v))
  }

  // Packaged as lemma. Proves trivially as ensures of KnownKeys,
  // but creates a trigger storm.
  lemma HostKeysSubsetOfKnownKeys(v: Variables)
    requires v.WF()
    ensures forall idx | 0 <= idx < v.mapCount() :: v.maps[idx].Keys <= KnownKeys(v)
  {
    forall idx | 0 <= idx < v.mapCount() ensures v.maps[idx].Keys <= KnownKeys(v)
    {
      UnionSeqOfSets_auto<Key>();
      assert v.maps[idx].Keys == MapDomains(v)[idx];  // trigger
    }
  }

  lemma KnownKeyHasOwner(v: Variables, key: Key) returns (hostIdx: nat)
    requires v.WF()
    requires key in KnownKeys(v)
    ensures HostHasKey(v, hostIdx, key)
  {
    EachUnionMemberBelongsToASet(MapDomains(v));
    var i:nat :| 0 <= i < |MapDomains(v)| && key in MapDomains(v)[i];
    hostIdx := i;
  }

  ghost function Abstraction(v: Variables) : MapSpec.Variables
    requires v.WF()
  {
    // DONE: fill in here (solution: 1 line)
    MapSpec.Variables(
      map k: Key | k in KnownKeys(v) :: AbstractionOneKey(v, k)
    ) // Replace me
    // END EDIT
  }

  ghost predicate KeysHeldUniquely(v: Variables)
    requires v.WF()
  {
    forall key, hostidx:HostIdx, otherhost:HostIdx
      // Previously, the solution had this whole predicate opaque. In this demo
      // I opted to instead give it a more restrictive trigger - I believe it
      // would be fine to go with the auto-generated one, but this one is more
      // specific.
      {:trigger key in v.maps[hostidx], v.maps[otherhost]}
      | && v.ValidHost(hostidx) && v.ValidHost(otherhost)
        && key in v.maps[hostidx] && key in v.maps[otherhost]
      :: hostidx == otherhost
  }

  ghost predicate Inv(v: Variables)
  {
    // DONE: fill in here (solution: 5 lines)
    && v.WF()
    && KeysHeldUniquely(v)
    && KnownKeys(v) == AllKeys()
       // END EDIT
  }

  // FIXME: fill in here (solution: 9 lines)
  // add any helper lemmas you need here
  // END EDIT

  lemma RefinementInit(v: Variables)
    requires v.WF()
    requires Init(v)
    ensures MapSpec.Init(Abstraction(v))
    ensures Inv(v)
  {
    // FIXME: fill in here (solution: 1 line)
    // END EDIT
  }

  // Since we know that keys are held uniquely, if we've found a host that holds a key,
  // that can be the only solution to the 'choose' operation that defines KeyHolder.
  lemma AnyHostWithKeyIsKeyHolder(v: Variables, hostidx:HostIdx, key:Key)
    requires v.WF()
    requires KeysHeldUniquely(v)
    requires HostHasKey(v, hostidx, key)
    ensures KeyHolder(v, key) == hostidx
  {
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma InsertPreservesInvAndRefines(v: Variables, v': Variables, event: Event, step: Step)
    requires Inv(v)
    requires NextStep(v, v', event, step)
    requires step.InsertStep?
    ensures Inv(v')
    ensures MapSpec.Next(Abstraction(v), Abstraction(v'), event)
  {
    // FIXME: fill in here (solution: 56 lines)
    var hostIdx := step.idx;
    assert event.PutEvent?;
    var key := step.key;
    var value := step.value;
    // END EDIT
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma QueryPreservesInvAndRefines(v: Variables, v': Variables, event: Event, step: Step)
    requires Inv(v)
    requires NextStep(v, v', event, step)
    requires step.QueryStep?
    ensures Inv(v')
    ensures MapSpec.Next(Abstraction(v), Abstraction(v'), event)
  {
    // FIXME: fill in here (solution: 6 lines)
    var hostIdx := step.idx;
    assert event.GetEvent?;
    var key := step.key;
    assert event.value == v.maps[step.idx][key];
    assert v == v';
    assert v.ValidHost(hostIdx);
    assert Abstraction(v) == Abstraction(v');
    assert key in KnownKeys(v) by {
      HostKeysSubsetOfKnownKeys(v);
      assert key in v.maps[hostIdx];
    }
    assert Abstraction(v).mapp[key] == AbstractionOneKey(v, key);
    assert HostHasKey(v, hostIdx, key);
    assert KeyHolder(v, key) == hostIdx;
    assert key in Abstraction(v).mapp;
    assert event.value == Abstraction(v).mapp[key];
    // END EDIT
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma TransferPreservesInvAndRefines(v: Variables, v': Variables, event: Event, step: Step)
    requires Inv(v)
    requires NextStep(v, v', event, step)
    requires step.TransferStep?
    ensures Inv(v')
    ensures MapSpec.Next(Abstraction(v), Abstraction(v'), event)
  {
    // FIXME: fill in here (solution: 56 lines)
    assert event.NoOpEvent?;

    var sendIdx := step.sendIdx;
    var recvIdx := step.recvIdx;
    var key0 := step.key;

    assert KnownKeys(v) <= KnownKeys(v') by {
      assert key0 in v.maps[sendIdx];
      assert key0 in v'.maps[recvIdx];
      assert HostHasKey(v, sendIdx, key0);
      forall key | key in KnownKeys(v)
        ensures key in KnownKeys(v') {
          if key == key0 {
            assert key in v'.maps[recvIdx];
            var hostIdx := KnownKeyHasOwner(v, key);
            assert hostIdx == sendIdx;
            // assert key in KnownKeys(v') by {
            //   HostKeysSubsetOfKnownKeys(v');
            // }
          } else {
            assert key in KnownKeys(v);
            // var hostIdx := KnownKeyHasOwner(v, key);
            // assert hostIdx != sendIdx by {
            // }
            // assert HostHasKey(v', hostIdx, key);
            assert key in KnownKeys(v') by {
              HostKeysSubsetOfKnownKeys(v');
            }
          }
        }
    }

    assert KnownKeys(v') <= KnownKeys(v);

    assert KnownKeys(v) == KnownKeys(v');

    forall key |  key in KnownKeys(v)
    ensures AbstractionOneKey(v, key) == AbstractionOneKey(v', key)
    {}
    assert Abstraction(v) == Abstraction(v');
    // END EDIT
  }

  // This is your proof goal.
  // You'll need a case analysis on the different kinds of steps to prove
  // it.
  lemma RefinementNext(v: Variables, v': Variables, event: Event)
    requires Inv(v)
    requires Next(v, v', event)
    ensures Inv(v')
    ensures MapSpec.Next(Abstraction(v), Abstraction(v'), event)
  {
    // Use InsertPreservesInvAndRefines, QueryPreservesInvAndRefines, and
    // TransferPreservesInvAndRefines here to complete this proof.
    // FIXME: fill in here (solution: 11 lines)
    // END EDIT
  }
}
