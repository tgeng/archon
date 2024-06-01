Let(
  t = Def(qn = qn"__unresolved__.getA") @ "getA",
  tBinding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
    usage = Collapse(cTm = Def(qn = qn"__unresolved__.uA") @ "uA") @ "ε"
  ) @ "a",
  eff = Collapse(cTm = Def(qn = qn"__unresolved__.effA") @ "effA") @ "ε",
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    tBinding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"__unresolved__.uB") @ "uB") @ "ε"
    ) @ "b",
    eff = Collapse(cTm = Def(qn = qn"__unresolved__.effB") @ "effB") @ "ε",
    body = Let(
      t = Return(v = Var(idx = 0) @ "b", usage = Auto() @ "ε") @ "b",
      tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(
        t = Let(
          t = Return(v = Var(idx = 2) @ "a", usage = Auto()) @ "a",
          tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
          eff = Auto(),
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