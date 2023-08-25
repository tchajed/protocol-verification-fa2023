// Verifying imperative code

// We'll briefly explore how to write and specify imperative code. We won't use
// this in the rest of the class, but it'll provide a useful grounding for
// thinking about specifications. Furthermore we will be writing lemmas, which
// are (surprisingly!) very much like methods.

ghost predicate IsEven(x:int)
{
  x/2*2==x
}

// A method is like a C function; it can return values. Let's return a value
// and then ensure a property of it.
method ExplainEvenNumbers(x:int) returns (half_x:int)
  // This method doesn't work unless we know x is even.
  // This requires clause is a fact we get to assume inside the method.
  requires IsEven(x)
  // To specify what a method does, we write a _postcondition_ with an "ensures" clause.
  ensures half_x*2 == x
{
  // return half_x by assigning it.
  // FIXME: fill in here (solution: 1 line)
   half_x := 1;
  // END EDIT
}

ghost predicate AlternateEven(x:int)
{
  exists half_x :: half_x * 2 == x
}

// Instead of hiding the thing we prove inside the body as an assert,
// let's export it.
lemma EvenDefinitionsAreEquivalent(x:int)
  ensures IsEven(x) == AlternateEven(x)
{
  // Wow, that proved without us providing a witness!
}

// Implementing a recursive function.

// This function is defined using "function" rather than "ghost function", which
// means Dafny will also allow compiling it to executable code in a language
// like C# or Java (among other supported languages).
//
// Define fibo(n) to be the nth Fibonacci number. The first few numbers in this
// sequence are 0, 1, 2, 3, 5, 8, 13, ... (each number is the sum of the
// previous two, except for the base cases).
function fibo(n:nat) : nat
{
  // FIXME: fill in here (solution: 3 lines)
        0
  // END EDIT
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(20) == 6765
{
}

// =========================================
// Binary search
// =========================================

ghost predicate IsSorted(seqint:seq<int>) {
  forall i:nat,j:nat | i < j < |seqint| :: seqint[i] <= seqint[j]
}

// Write down the BinarySearch algorithm, which should return the index of the
// first element of the haystack that is >= to the needle.  If the
// needle is present, this should be the index of the needle.  If needle is
// bigger than every element, return the length of the sequence: it's not a
// valid index in the sequence, but it's bigger than the indices of all the
// elements that have smaller values.

method BinarySearch(haystack:seq<int>, needle:int) returns (index:nat)
  requires IsSorted(haystack)
  // Translate the above English specification to a postcondition (you
  // can use multiple ensures clauses). Remember that haystack[i] is the ith
  // element of the haystack and |haystack| is its length.
  // FIXME: fill in here (solution: 3 lines)
  // Add ensures clauses here
  // END EDIT

{
  // FIXME: fill in here (solution: 11 lines)
   return 0;  // Replace me with an implementation.
  // END EDIT
}


method UseBinarySearch() {
  var a := [1, 3,5,9];
  // this assertion is implied by the call to BinarySearch
  assert IsSorted(a);
  var x := BinarySearch(a, 4);
  // The 1st element is less than the needle and the next element is larger, so
  // BinarySearch's specification implies the return value is 2.
  //
  // Note that this proof _only_ uses BinarySearch's specification, not its
  // implementation. This might seem inconvenient but it gives useful
  // abstraction and information hiding: the implementation of BinarySearch can
  // export exactly what it wants (which might not have to change in the future
  // even if the implementation improves), and the caller can rely on a property
  // that's simpler to understand than the full implementation details.
  //
  // The result is that until you have a sufficiently detailed specification
  // this proof won't go through, even if your implementation is correct.
  // Conversely if you have the right specification this proof will go through
  // even if BinarySearch isn't yet verified.
  assert a[1] < 4;
  assert a[2] >= 4;
  assert x == 2;
}
