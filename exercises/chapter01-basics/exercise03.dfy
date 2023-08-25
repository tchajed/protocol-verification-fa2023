// Algebraic datatypes
//
// In order to define more interesting things, we'll need to start constructing
// our own datatypes. Dafny provides "algebraic datatypes" which will be handy
// for doing just that.

// Eventually we'll use datatypes defined in these two files. They're in
// separate files since we use them later in the course. You won't need to refer
// to them until later in this file (we'll point out when).
//
// Files must be included before any other definitions, that's why this appears
// here.
include "DirectionsLibrary.dfy"
include "LunchLibrary.dfy"

// ==========================================================
// Struct (product) datatypes.
// ==========================================================

// First, structs (products):
datatype Point = PointCtor(x:int, y:int)

// You could alternatively write this as:
//   datatype Point = Point(x:int, y:int)
// The first "Point" is the type name, the second is the constructor name. When
// the type has only one constructor, it's conventional to give them the same
// name since the language can distinguish the two uses from context.

// FIXME: fill in here (solution: 4 lines)
 ghost function subtractPoints(tip:Point, tail:Point) : Point
 {
   PointCtor(tip.x - tail.x, tip.y - tail.x)
 }
// END EDIT

lemma PointArithmetic()
{
  var a := PointCtor(1,13);
  var b := PointCtor(2,7);

  // NB Points (and every other `datatype`) are mathematical, immutable
  // objects, so the one we get back from the function must be equal
  // (identical) to the one we construct manually. There's no implicit
  // user-overridable Equals() method; these are platonic mathematical objects.

  // This exercise is a little harder than the previous ones; take a moment
  // to investigate it carefully!
  assert subtractPoints(a, b) == PointCtor(-1, 6);
}

// ==========================================================
// Union (sum) datatypes
// ==========================================================

// This defines a datatype Light that has three _variants_: Red, Green, and
// Yellow.
datatype Light = Red() | Green() | Yellow()

lemma ExampleUsingLightType() {
  var l: Light := Green();
  // each variant is different from the others
  assert l != Yellow();
  // we can also write variants without parentheses
  assert l == Green;
}

// Take a look at DirectionsLibrary.dfy. We'll use it for the next exercise (and
// it teaches you a bit more about union types)

lemma TwoWrongsDontMakeARight(dir:Direction)
{
  // FIXME: fill in here (solution: 1 line)
   assert TurnLeft(TurnLeft(TurnLeft(dir))) == TurnRight(TurnRight(dir));
  // END EDIT
}

// Next, take a look at LunchLibrary.dfy. It defines more datatypes, combining
// the features of structs and unions seen above.

lemma AlgebraicLunch()
{
  var meal:set<Order> := {
    Pizza(Ham, Olive),
    Sandwich(Ham, Provolone),
    Pizza(Ham, Olive)
  };
  // Fix this assertion. Hint: The two pizzas are the same element of the datatype.
  // FIXME: fill in here (solution: 1 line)
   assert |meal| == 3;
  // END EDIT
}
