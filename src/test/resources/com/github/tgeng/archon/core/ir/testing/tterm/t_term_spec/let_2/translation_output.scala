Let(
  t = Def(qn = qn"__unresolved__.getA") @ "getA",
  tBinding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "A",
    usage = Collapse(cTm = Def(qn = qn"__unresolved__.uA") @ "uA") @ "uA"
  ) @ "a",
  eff = Collapse(cTm = Def(qn = qn"__unresolved__.effA") @ "effA") @ "effA",
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    tBinding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "B",
      usage = Collapse(cTm = Def(qn = qn"__unresolved__.uB") @ "uB") @ "uB"
    ) @ "b",
    eff = Collapse(cTm = Def(qn = qn"__unresolved__.effB") @ "effB") @ "effB",
    body = Redex(
      t = Def(qn = qn"__unresolved__.plus") @ "plus",
      elims = List(ETerm(v = Var(idx = 1) @ "a"), ETerm(v = Var(idx = 0) @ "b"))
    ) @ "plus a b"
  ) @ """let b: <effB> [uB] B = getB
plus a b"""
) @ """let a: <effA> [uA] A = getA
let b: <effB> [uB] B = getB
plus a b"""