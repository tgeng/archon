Let(
  t = Def(qn = qn"__unresolved__.d") @ "d",
  ty = Auto() @ "ε",
  eff = Auto(),
  usage = Auto(),
  body = Redex(
    t = Let(
      t = Def(qn = qn"__unresolved__.c") @ "c",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Redex(
        t = Let(
          t = Def(qn = qn"__unresolved__.b") @ "b",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Redex(
            t = Let(
              t = Def(qn = qn"__unresolved__.a") @ "a",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
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