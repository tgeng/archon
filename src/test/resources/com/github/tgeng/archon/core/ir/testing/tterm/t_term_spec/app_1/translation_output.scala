Let(
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
                        t = Def(qn = qn"__unresolved__.f") @ "f",
                        elims = List(ETerm(v = Var(idx = 0) @ "ε"))
                      ) @ "f a",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
                    ) @ "ε"
                  ) @ "ε",
                  elims = List(ETerm(v = Var(idx = 0)))
                ) @ "f a b",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε",
            elims = List(ETerm(v = Var(idx = 0)))
          ) @ """f a b
  c""",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      ) @ "ε",
      elims = List(ETerm(v = Var(idx = 0)))
    ) @ """f a b
  c d""",
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Return(v = Var(idx = 0), usage = Auto())
  ) @ "ε"
) @ "ε"