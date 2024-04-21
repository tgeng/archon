Let(
  t = Def(qn = qn"__unresolved__.A") @ "A",
  ty = Auto() @ "ε",
  eff = Auto(),
  usage = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.effA") @ "effA",
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.uA") @ "uA",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = Let(
          t = Def(qn = qn"__unresolved__.getA") @ "getA",
          ty = Var(idx = 0) @ "ε",
          eff = Var(idx = 0),
          usage = Var(idx = 0),
          body = Let(
            t = Def(qn = qn"__unresolved__.B") @ "B",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Def(qn = qn"__unresolved__.effB") @ "effB",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = Def(qn = qn"__unresolved__.uB") @ "uB",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Let(
                  t = Let(
                    t = Def(qn = qn"__unresolved__.getB") @ "getB",
                    ty = Var(idx = 0),
                    eff = Var(idx = 0),
                    usage = Var(idx = 0),
                    body = Let(
                      t = Redex(
                        t = Let(
                          t = Redex(
                            t = Def(qn = qn"__unresolved__.plus") @ "plus",
                            elims = List(ETerm(v = Var(idx = 5) @ "a"))
                          ) @ "plus a",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
                        ) @ "ε",
                        elims = List(ETerm(v = Var(idx = 0) @ "b"))
                      ) @ "plus a b",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Return(v = Var(idx = 0), usage = Auto())
                    ) @ "ε"
                  ) @ """let b: <effB> [uB] B = getB
plus a b""",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε"
              ) @ "ε"
            ) @ "ε"
          ) @ "ε"
        ) @ """let a: <effA> [uA] A = getA
let b: <effB> [uB] B = getB
plus a b""",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0), usage = Auto())
      ) @ "ε"
    ) @ "ε"
  ) @ "ε"
) @ "ε"