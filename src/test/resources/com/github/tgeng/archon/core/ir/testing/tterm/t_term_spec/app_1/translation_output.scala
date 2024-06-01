Let(
  t = Def(qn = qn"__unresolved__.d") @ "d",
  tBinding = Binding(ty = Auto() @ "ε", usage = Auto()) @ "$v",
  eff = Auto(),
  body = Redex(
    t = Let(
      t = Def(qn = qn"__unresolved__.c") @ "c",
      tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(
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
                t = Def(qn = qn"__unresolved__.f") @ "f",
                elims = List(ETerm(v = Var(idx = 0) @ "ε"))
              ) @ "f a"
            ) @ "ε",
            elims = List(ETerm(v = Var(idx = 0)))
          ) @ "f a b"
        ) @ "ε",
        elims = List(ETerm(v = Var(idx = 0)))
      ) @ """f a b
  c"""
    ) @ "ε",
    elims = List(ETerm(v = Var(idx = 0)))
  ) @ """f a b
  c d"""
) @ "ε"