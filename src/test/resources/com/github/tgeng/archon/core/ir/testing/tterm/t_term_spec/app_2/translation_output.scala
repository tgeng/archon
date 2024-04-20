Let(
  t = Let(
    t = Def(qn = qn"__unresolved__.d") @ "d",
    ty = Auto() @ "ε",
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Redex(
        t = Let(
          t = Def(qn = qn"__unresolved__.c") @ "c",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = Redex(
              t = Def(qn = qn"__unresolved__.h") @ "h",
              elims = List(ETerm(v = Var(idx = 0) @ "ε"))
            ) @ "h c",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
          ) @ "ε"
        ) @ "ε",
        elims = List(ETerm(v = Var(idx = 0)))
      ) @ "h c d",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε"
  ) @ "ε",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Let(
    t = Redex(
      t = Let(
        t = Let(
          t = Def(qn = qn"__unresolved__.b") @ "b",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = Redex(
              t = Let(
                t = Def(qn = qn"__unresolved__.a") @ "a",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Let(
                  t = Redex(
                    t = Def(qn = qn"__unresolved__.g") @ "g",
                    elims = List(ETerm(v = Var(idx = 0)))
                  ) @ "g a",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε"
              ) @ "ε",
              elims = List(ETerm(v = Var(idx = 0)))
            ) @ "g a b",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Return(v = Var(idx = 0), usage = Auto())
          ) @ "ε"
        ) @ "ε",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Let(
          t = Redex(t = Def(qn = qn"__unresolved__.f") @ "f", elims = List(ETerm(v = Var(idx = 0)))) @ """f
  (g a b""",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      ) @ "ε",
      elims = List(ETerm(v = Var(idx = 0)))
    ) @ """f
  (g a b)
  (h c d""",
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Return(v = Var(idx = 0), usage = Auto())
  ) @ "ε"
) @ "ε"