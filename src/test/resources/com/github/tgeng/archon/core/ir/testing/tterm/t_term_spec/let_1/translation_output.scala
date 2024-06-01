Let(
  t = Def(qn = qn"__unresolved__.getA") @ "getA",
  tBinding = Binding(
    ty = Auto() @ """let a = getA
let b = getB
plus a b""",
    usage = Collapse(
      cTm = Return(v = Auto(), usage = Auto() @ "ε") @ """let a = getA
let b = getB
plus a b"""
    ) @ "ε"
  ) @ "a",
  eff = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.getB") @ "getB",
    tBinding = Binding(
      ty = Auto() @ """let b = getB
plus a b""",
      usage = Collapse(
        cTm = Return(v = Auto(), usage = Auto()) @ """let b = getB
plus a b"""
      )
    ) @ "b",
    eff = Auto(),
    body = Let(
      t = Return(v = Var(idx = 0) @ "b", usage = Auto()) @ "b",
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
  ) @ """let b = getB
plus a b"""
) @ """let a = getA
let b = getB
plus a b"""