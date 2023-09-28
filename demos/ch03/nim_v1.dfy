// Nim version 1: not in Jay Normal Form (no Step datatype)

datatype Player = P1 | P2
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {
  && |v.piles| == 3
  && v.turn.P1? // syntax
}

ghost predicate TakeTurn(v: Variables, v': Variables) {
  exists take: nat, p: nat ::
    && p < |v.piles|
    && take <= v.piles[p]
    && v'.piles == v.piles[p := v.piles[p] - take]
}

ghost predicate Next(v: Variables,  v': Variables) {
  || TakeTurn(v, v')
}
