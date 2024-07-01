Let(
  t = Def(qn = qn"__unresolved__.a") @ "a",
  tBinding = Binding(ty = Auto() @ "ε", usage = Auto()) @ "$v",
  eff = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.b") @ "b",
    tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
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
          t = Def(qn = qn"__unresolved__.f") @ "f",
          elims = List(
            ETerm(v = Var(idx = 3) @ "a"),
            ETerm(v = Var(idx = 2) @ "b"),
            ETerm(v = Var(idx = 1) @ "c"),
            ETerm(v = Var(idx = 0) @ "d")
          )
        ) @ """f a b
  c d"""
      ) @ "ε"
    ) @ "ε"
  ) @ "ε"
) @ "ε"