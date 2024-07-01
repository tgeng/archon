Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.a") @ "a",
    tBinding = Binding(ty = Auto() @ "ε", usage = Auto()) @ "$v",
    eff = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.b") @ "b",
      tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(
        t = Def(qn = qn"__unresolved__.f") @ "f",
        elims = List(ETerm(v = Var(idx = 1) @ "a"), ETerm(v = Var(idx = 0) @ "b"))
      ) @ "f a b"
    ) @ "ε"
  ) @ "ε",
  tBinding = Binding(
    ty = Auto(),
    usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u0") @ "ε") @ "ε"
  ) @ "_",
  eff = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.c") @ "c",
    tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
    eff = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.d") @ "d",
      tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(
        t = Def(qn = qn"__unresolved__.g") @ "g",
        elims = List(ETerm(v = Var(idx = 1) @ "c"), ETerm(v = Var(idx = 0) @ "d"))
      ) @ "g c d"
    ) @ "ε"
  ) @ "ε"
) @ """f a b
g c d"""