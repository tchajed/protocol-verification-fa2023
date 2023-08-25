// Built-in data types
//
// We walk through a few of Dafny's built-in data types that are useful to model
// real protocols.

// ==========================================================
// Sets
// ==========================================================

// This predicate takes a set of integers as an argument.
// set<T> is a built-in templated type.
ghost predicate HasSevenAndNotNine(intset:set<int>)
{
  7 in intset && 9 !in intset
}

lemma TryOutSomeSetLiterals()
{
  assert {1,3,8} == {8,1,3};

  assert HasSevenAndNotNine({7});

  // None of these asserions are correct. Try them.
  // Then delete these first two...
  // FIXME: fill in here (solution: 0 lines)
   assert HasSevenAndNotNine({7,9});
   assert HasSevenAndNotNine({1,3,5,7,8,9,10});
  // END EDIT

  // ...and replace the argument of this assert with a set that does satisfy
  // the predicate.
  // FIXME: fill in here (solution: 1 line)
   assert HasSevenAndNotNine({});
  // END EDIT
}

// <= on sets is subset.
ghost predicate HasFourFiveSix(intset:set<int>)
{
  {6,5,4} <= intset  // I can because they're sets!
}

lemma SomeAssertionsAboutSets()
{
  assert !HasFourFiveSix({1,2,4,6,7});

  /*
    This is just a mathematical "let" statement.
    It's safe to substitute the value wherever "happySet" appears.
  */
  var happySet := {1,2,4,6,7,5};
  assert HasFourFiveSix(happySet);

  /* - on sets is difference. */
  assert happySet - {4,5,6} == {7,2,1};

  /* + on sets is union. */
  assert HasFourFiveSix({4, 6} + {5});

  /*
    |x| on a set is cardinality.
    (set<T> is always finite; there is another type iset<T> for
    possibly-infinite sets.)
  */
  // FIXME: fill in here (solution: 1 line)
   assert |happySet| == 7;
  // END EDIT
}

lemma ExperimentsWithSequences()
{
  // [x,y,z] is a literal sequence; this one is a seq<int>.
  var fibo := [1,1,2,3,5,8,13,21,34];
  // Index into a sequence.
  assert fibo[4] == 5;

  // Sequences have finite length, accessed with the same cardinality syntax as
  // for set cardinality.
  assert |fibo| == 9;
  assert fibo[0] == 1;
  assert fibo[8] == 34;
  // FIXME: fill in here (solution: 1 line)
   assert fibo[9] == 21;
  // END EDIT
}

// ==========================================================
// Sequence operations
// ==========================================================

lemma ExperimentsWithSequenceSlicing()
{
  var fibo := [1,1,2,3,5,8,13,21,34];

  // A slice of a sequence is a sequence.
  // The left argument is inclusive, the right exclusive.
  assert fibo[2..4] == [2,3];

  // You can omit either endpoint to refer to the beginning or end of the
  // sequence.
  assert fibo[..3] == [1,1,2];
  assert fibo[7..] == [21,34];

  // Uncomment the following line and see what error you get. (Then delete the
  // line to fix the error.)
  // FIXME: fill in here (solution: 0 lines)
  // assert fibo[5..6] == 8;
  // END EDIT

  // FIXME: fill in here (solution: 1 line)
   assert fibo[5..6] == [8,13];
  // END EDIT
}

lemma ExperimentsWithSequenceTypes()
{
  var fibo := [1,1,2,3,5,8,13,21,34];

  // The type of fibo is seq<int>.
  // Here, we explicitly declare the type of `copy`. In previous examples, the
  // type has always been inferred by the compiler. I just wanted you to see
  // what it was inferring.
  var copy:seq<int> := fibo;

  // You can, of course, have a seq of other stuff.
  var seqOfSets:seq<set<int>> := [{0}, {0,1}, {0,1,2}];

  // Uncomment this line, see the type checking error, and fix it. (We give this
  // to you commented out because Dafny won't report verification errors until
  // all type errors are fixed, which would make the above exercises
  // impossible.)
  // FIXME: fill in here (solution: 1 line)
  // var whatsMyProblem := [0, 1, 2, false];
  // END EDIT

  assert |seqOfSets| == 3;
  // Type checking means the |expr| below is a set-cardinality operator.
  // FIXME: fill in here (solution: 1 line)
   assert |seqOfSets[1]| == 3;
  // END EDIT
}
