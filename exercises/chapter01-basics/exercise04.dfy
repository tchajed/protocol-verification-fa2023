// Quantified logical statements
//
// In this exericise we'll see forall and exists, which allow us to write
// interesting logical statements in specifications and to define protocols.

include "DirectionsLibrary.dfy"
include "LunchLibrary.dfy"

// Most of what we'll be working with in proof are quantified
// statements: for all inputs, my program produces the right output!
lemma Forall()
{
  assert forall x:int :: x+x == 2*x;
}

lemma ForallAssertionExamples()
{
  // These assertions are different from what we'd normally have in a
  // programming language because they aren't _executable_. These are
  // mathematical assertions that can be checked statically, but not by simply
  // running them since they talk about all integers.
  assert forall x: int :: x + 1 > x;
  assert forall x: int, y: int :: x + y == y + x;
  assert forall b: bool :: b || !b;
  // (you will get a warning "No terms found to trigger on" for these examples,
  // which is safe to ignore in this case)
}

/* Here's an example of proving a forall: */

function abs(x: int): int {
  if x < 0 then -x else x
}

lemma AbsLargerForAll()
  ensures forall x: int :: abs(x) >= x
{
  // New feature (forall statement): a _forall statement_ allows us to help Dafny with a proof of
  // `forall x :: ...` by talking about an individual `x` */
  forall x: int
    ensures abs(x) >= x
  {
    // Within the body of a forall statement, the proof can refer to `x` when
    // proving the ensures clause, which means we can call lemmas, do `if` case
    // splits, etc.
    if x < 0 {
      assert abs(x) == -x;
    }
  }
}

// Remember this critter from exercise12? We can rewrite it in a forall.
lemma AnotherForall()
{
  // "Two wrongs don't make a right, but ..."
  // FIXME: fill in here (solution: 1 line)
   assert forall dir :: TurnLeft(TurnLeft(TurnLeft(dir))) == TurnRight(TurnRight(dir));
  // END EDIT
}

// It's extremely common to have logical statements of the form `forall x ::
// P(x) ==> Q(x)`, which says that if P(x) is true, then Q(x) is true. Dafny has
// a special syntax that can make these conditional statements easier to read:
// `forall x | P(x) :: Q(x)` means the exact same thing.

// These two lines define P and Q as arbitrary predicates for the next example.
// Dafny won't assume anything about their definitions except that they are
// deterministic.
predicate P(x: int)
predicate Q(x: int)

lemma ForallConditionalSyntax()
  ensures (forall x: int :: P(x) ==> Q(x)) <==>
          (forall x: int | P(x) :: Q(x))
{
}

lemma ForallConditionalExercise()
  ensures (forall x: int | x < 5 && P(x) :: Q(x)) <==>
          // write an equivalent forall without using the | syntax
          // FIXME: fill in here (solution: 1 line)
           (forall x: int :: true)
          // END EDIT
{}

// Here's there-exists, the "dual" of forall.
// (exists x :: P(x)) <==> !(forall x :: !P(x))
lemma TryThatCheeseOnASandwich()
{
  // Hey, neat. Dafny has a hard time proving exists. It needs
  // a "witness".
  // To proceed, comment out this assertion for now and read on for how to solve it.
  // (If the '?' syntax is surprising, go (re-)read DirectionsLibrary.dfy.)
  // FIXME: fill in here (solution: 2 lines)
   assert (forall o1:Order | o1.Appetizer? ::
             exists o2:Order :: o2.Sandwich? && o1.cheese == o2.cheese);
  // END EDIT
}

lemma CheeseTakeTwo()
{
  // So here's the "statement" version of a forall expression.
  // With nothing in the body, it's exactly equivalent to the assertion
  // above.
  forall o1:Order
    // The assumptions follow a '|' ("such that")
    | o1.Appetizer?
    // The conclusions follow an "ensures" keyword (replacing :: in the expression)
    ensures exists o2:Order :: o2.Sandwich? && o1.cheese == o2.cheese
  {
    // The body of the forall statement is a proof context for the
    // statement's conclusion. Inside here, o1 is defined, and we
    // can use it to complete the proof.

    // But how? What's missing is that Dafny needs a "witness" to the
    // there-exists. We need to show an expression that satisfies the
    // body of the exists. Try uncommenting these lines:
    // FIXME: fill in here (solution: 2 lines)
    // var o3 := Sandwich(Ham, o1.cheese);
    // assert o3.Sandwich? && o1.cheese == o3.cheese;
    // END EDIT
    // Simply *mentioning* an Order that satisfies the predicate
    // on o2 above is enough for Dafny to see the proof; once we mention
    // it, Dafny will try plugging it into the expression. Try removing
    // the assertion above this comment but leaving the var o3 ... line; notice
    // that the proof still goes through.
  }
}
