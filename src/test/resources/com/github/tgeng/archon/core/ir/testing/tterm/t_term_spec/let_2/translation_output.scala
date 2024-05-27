Let(
  t = Def(qn = qn"__unresolved__.getA") @ "getA",
  ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
  eff = Collapse(cTm = Def(qn = qn"__unresolved__.effA") @ "effA") @ "ε",
  usage = Collapse(cTm = Def(qn = qn"__unresolved__.uA") @ "uA") @ "ε",
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
    eff = Collapse(cTm = Def(qn = qn"__unresolved__.effB") @ "effB") @ "ε",
    usage = Collapse(cTm = Def(qn = qn"__unresolved__.uB") @ "uB") @ "ε",
    body = Let(
      t = Return(v = Var(idx = 0) @ "b", usage = Auto() @ "ε") @ "b",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Redex(
        t = Let(
          t = Return(v = Var(idx = 2) @ "a", usage = Auto()) @ "a",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Redex(
            t = Def(qn = qn"__unresolved__.plus") @ "plus",
            elims = List(ETerm(v = Var(idx = 0) @ "ε"))
          ) @ "plus a"
        ) @ "ε",
        elims = List(ETerm(v = Var(idx = 0)))
      ) @ "plus a b"
    ) @ "ε"
  ) @ """let b: <effB> [uB] B = getB
plus a b"""
) @ """let a: <effA> [uA] A = getA
let b: <effB> [uB] B = getB
plus a b"""