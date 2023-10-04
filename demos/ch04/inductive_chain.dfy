module Ex {

  datatype Variables = Variables(p1: bool, p2: bool, p3: bool, p4: bool)

  ghost predicate Init(v: Variables) {
    && !v.p1
    && !v.p2
    && !v.p3
    && !v.p4
  }

  datatype Step =
    | Step1
    | Step2
    | Step3
    | Step4

  ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      // ordinarily we'd have a predicate for each step, but in this simple
      // example it's easier to see everything written in one place
      case Step1 =>
        !v.p1 && v' == v.(p1 := true)
      case Step2 =>
        v.p1 && v' == v.(p2 := true)
      case Step3 =>
        v.p2 && v' == v.(p3 := true)
      case Step4 =>
        v.p3 && v' == v.(p4 := true)
    }
  }

  ghost predicate Next(v: Variables, v': Variables)
  {
    exists step: Step :: NextStep(v, v', step)
  }

  ghost predicate Safety(v: Variables)
  {
    v.p4 ==> v.p1
  }

  ghost predicate Inv(v: Variables)
  {
    && Safety(v)
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v) && Next(v, v')
    ensures Inv(v')
  {
    var step :| NextStep(v, v', step);
    match step {
      case Step1 => { return; }
      case Step2 => { return; }
      case Step3 => { return; }
      case Step4 => { return; }
    }
  }

  lemma InvSafe(v: Variables)
    ensures Inv(v) ==> Safety(v)
  {
    return;
  }

  lemma SafetyHolds(v: Variables, v': Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
    if Inv(v) && Next(v, v') {
      InvInductive(v, v');
    }
    InvSafe(v);
  }
}
