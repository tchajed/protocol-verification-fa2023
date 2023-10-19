method Triple(q: int) returns (r: int)
  ensures r == q * 3
{
  var x := q + q;
  r := x + q;
}
