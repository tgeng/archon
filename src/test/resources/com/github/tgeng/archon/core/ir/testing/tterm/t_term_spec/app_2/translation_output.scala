Let(
  t = Let(
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
          t = Def(qn = qn"__unresolved__.h") @ "h",
          elims = List(ETerm(v = Var(idx = 0) @ "ε"))
        ) @ "h c"
      ) @ "ε",
      elims = List(ETerm(v = Var(idx = 0)))
    ) @ "h c d"
  ) @ "ε",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Redex(
    t = Let(
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
              t = Def(qn = qn"__unresolved__.g") @ "g",
              elims = List(ETerm(v = Var(idx = 0)))
            ) @ "g a"
          ) @ "ε",
          elims = List(ETerm(v = Var(idx = 0)))
        ) @ "g a b"
      ) @ "ε",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Redex(t = Def(qn = qn"__unresolved__.f") @ "f", elims = List(ETerm(v = Var(idx = 0)))) @ """f
  (g a b"""
    ) @ "ε",
    elims = List(ETerm(v = Var(idx = 0)))
  ) @ """f
  (g a b)
  (h c d"""
) @ "ε"