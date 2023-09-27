// You are asked to define the state machine for a coke vending machine.
// The machine starts empty and has a maximum capacity of 7 cokes.
// The machine should support the following actions:
// Purchase: dispense one coke from the machine
// Restock: add a number of cokes to the machine

datatype Variables = Variables(capacity: int, numCokes:int)

ghost predicate Init(v:Variables) {
  // FIXME: fill in here (solution: 2 lines)
      true // Replace me
  // END EDIT
}

ghost predicate Purchase(v:Variables, v':Variables) {
  // FIXME: fill in here (solution: 2 lines)
      true // Replace me
  // END EDIT
}

ghost predicate Restock(v:Variables, v':Variables, numRestock:int)
{
  // FIXME: fill in here (solution: 3 lines)
      true // Replace me
  // END EDIT
}

// Jay-Normal-Form: pack all the nondeterminism into a single object
datatype Step =
  | PurchaseStep
  | RestockStep(num: int)

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  case PurchaseStep => Purchase(v, v')
  case RestockStep(num) => Restock(v, v', num)
}

// This is a sanity check on your definitions and use of Step. If the proof
// fails, you have some non-determinism that was probably intentional: perhaps
// you failed to constrain one of the fields of v' in a transition, for example.
//
// You should not need to add any additional proof to this lemma's body.
lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.

ghost predicate Inv(v:Variables) {
  0 <= v.numCokes <= v.capacity
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Inv(v)
  ensures forall v, v' | Inv(v) && Next(v, v') :: Inv(v')
{
  forall v, v' | Inv(v) && Next(v, v')
    ensures Inv(v')
  {
    if(Purchase(v, v')) {
      assert Inv(v');
    } else {
      var num :| Restock(v, v', num);
      assert Inv(v');
    }
  }
}

lemma NonTrivialPurchase()
  ensures exists v, v' :: Inv(v) && Next(v, v') && v'.numCokes + 1 == v.numCokes
{
  var v := Variables(capacity := 7, numCokes := 1);
  var v' := Variables(capacity := 7, numCokes := 0);
  assert NextStep(v, v', PurchaseStep);
  assert Inv(v) && Next(v, v') && v'.numCokes + 1 == v.numCokes;
}

lemma NonTrivialRestock()
  ensures exists v, v' :: Inv(v) && Next(v, v') && v.numCokes < v'.numCokes
{
  var v := Variables(capacity:= 7, numCokes:= 4);
  var v' := Variables(7, 7);
  assert NextStep(v, v', RestockStep(3));
  assert Inv(v) && Next(v, v') && v.numCokes < v'.numCokes;
}
