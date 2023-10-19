method Triple(q: int) returns (r: int)
  requires 3 < q
  ensures r == q * 3
{
  if q < 5 {
    r := 12;
  } else {
    r := q * 2;
    r := r + q;
  }
}
