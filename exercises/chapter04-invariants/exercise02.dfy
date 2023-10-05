// Single-Server Lock Service Proof

// We provide a correct spec for the lock server here, but leave you
// to define the Safety property to be proven.
// You are welcome to prove correct your own model from chapter03,
// but note that may be too hard or too easy if your spec is broken.

// Copy your solution for chapter03/exercise03 into the current directory with
// this name:
include "ch03exercise03.dfy"

// FIXME: fill in here (solution: 11 lines)
 ghost predicate Inv(v:Variables) {
   true // probably not strong enough :)
 }
// END EDIT

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(v:Variables, v':Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  // FIXME: fill in here (solution: 10 lines)
  // END EDIT
}
