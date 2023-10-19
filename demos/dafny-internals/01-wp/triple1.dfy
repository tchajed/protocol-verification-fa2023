method Triple(q: int) returns (r: int)
{
  var x := q + q;
  r := x + q;
  // encoding of postcondition
  assert r == q * 3;
}

// WP(Triple, true)
// == WP(x := q + q,
//       WP(r := x + q,
//          WP(assert r == q * 3,
//             true)))
// == WP(x := q + q,
//       WP(r := x + q,
//          r == q * 3 /\ true
//             true)))
// == WP(x := q + q,
//       x + q == q * 3 /\ true)
// == (q + q) + q == q * 3 /\ true
