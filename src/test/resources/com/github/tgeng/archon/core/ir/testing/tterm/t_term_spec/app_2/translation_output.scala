Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.d") @ "d",
    tBinding = Binding(ty = Auto() @ "ε", usage = Auto()) @ "$v",
    eff = Auto(),
    body = Redex(
      t = Let(
        t = Def(qn = qn"__unresolved__.c") @ "c",
        tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
        eff = Auto(),
        body = Redex(
          t = Def(qn = qn"__unresolved__.h") @ "h",
          elims = List(ETerm(v = Var(idx = 0) @ "ε"))
        ) @ "h c"
      ) @ "ε",
      elims = List(ETerm(v = Var(idx = 0)))
    ) @ "h c d"
  ) @ "ε",
  tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
  eff = Auto(),
  body = Redex(
    t = Let(
      t = Let(
        t = Def(qn = qn"__unresolved__.b") @ "b",
        tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
        eff = Auto(),
        body = Redex(
          t = Let(
            t = Def(qn = qn"__unresolved__.a") @ "a",
            tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
            eff = Auto(),
            body = Redex(
              t = Def(qn = qn"__unresolved__.g") @ "g",
              elims = List(ETerm(v = Var(idx = 0)))
            ) @ "g a"
          ) @ "ε",
          elims = List(ETerm(v = Var(idx = 0)))
        ) @ "g a b"
      ) @ "ε",
      tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(t = Def(qn = qn"__unresolved__.f") @ "f", elims = List(ETerm(v = Var(idx = 0)))) @ """f
  (g a b"""
    ) @ "ε",
    elims = List(ETerm(v = Var(idx = 0)))
  ) @ """f
  (g a b)
  (h c d"""
) @ "ε"