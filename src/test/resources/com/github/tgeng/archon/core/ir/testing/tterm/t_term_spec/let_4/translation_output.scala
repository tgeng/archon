Let(
  t = Return(
    v = Auto() @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
    usage = Auto() @ "ε"
  ) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Let(
    t = Return(v = Auto(), usage = Auto()),
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Return(v = Auto(), usage = Auto()),
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = Let(
          t = Let(
            t = Return(
              v = Auto() @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
              usage = Auto()
            ) @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Return(v = Auto(), usage = Auto()),
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = Return(v = Auto(), usage = Auto()),
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Let(
                  t = Let(
                    t = Def(qn = qn"__unresolved__.getA1") @ "getA1",
                    ty = Var(idx = 0) @ "ε",
                    eff = Var(idx = 0),
                    usage = Var(idx = 0),
                    body = Let(
                      t = Return(
                        v = Auto() @ """let a2 = getA2
  plus a1 a2""",
                        usage = Auto()
                      ) @ """let a2 = getA2
  plus a1 a2""",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Let(
                        t = Return(v = Auto(), usage = Auto()),
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Let(
                          t = Return(v = Auto(), usage = Auto()),
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Let(
                            t = Let(
                              t = Def(qn = qn"__unresolved__.getA2") @ "getA2",
                              ty = Var(idx = 0),
                              eff = Var(idx = 0),
                              usage = Var(idx = 0),
                              body = Let(
                                t = Return(v = Var(idx = 0) @ "a2", usage = Auto()) @ "a2",
                                ty = Auto(),
                                eff = Auto(),
                                usage = Auto(),
                                body = Let(
                                  t = Redex(
                                    t = Let(
                                      t = Return(v = Var(idx = 5) @ "a1", usage = Auto()) @ "a1",
                                      ty = Auto(),
                                      eff = Auto(),
                                      usage = Auto(),
                                      body = Let(
                                        t = Redex(
                                          t = Def(qn = qn"__unresolved__.plus") @ "plus",
                                          elims = List(ETerm(v = Var(idx = 0)))
                                        ) @ "plus a1",
                                        ty = Auto(),
                                        eff = Auto(),
                                        usage = Auto(),
                                        body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
                                      ) @ "ε"
                                    ) @ "ε",
                                    elims = List(ETerm(v = Var(idx = 0)))
                                  ) @ "plus a1 a2",
                                  ty = Auto(),
                                  eff = Auto(),
                                  usage = Auto(),
                                  body = Return(v = Var(idx = 0), usage = Auto())
                                ) @ "ε"
                              ) @ "ε"
                            ) @ """let a2 = getA2
  plus a1 a2""",
                            ty = Auto(),
                            eff = Auto(),
                            usage = Auto(),
                            body = Return(v = Var(idx = 0), usage = Auto())
                          ) @ "ε"
                        ) @ "ε"
                      ) @ "ε"
                    ) @ "ε"
                  ) @ """let a1 = getA1
  let a2 = getA2
  plus a1 a2""",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε"
              ) @ "ε"
            ) @ "ε"
          ) @ "ε",
          ty = Var(idx = 0),
          eff = Var(idx = 0),
          usage = Var(idx = 0),
          body = Let(
            t = Return(
              v = Auto() @ """let b = getB
plus a b""",
              usage = Auto()
            ) @ """let b = getB
plus a b""",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Return(v = Auto(), usage = Auto()),
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = Return(v = Auto(), usage = Auto()),
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
                      t = Return(v = Var(idx = 0) @ "b", usage = Auto()) @ "b",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Let(
                        t = Redex(
                          t = Let(
                            t = Return(v = Var(idx = 5) @ "a", usage = Auto()) @ "a",
                            ty = Auto(),
                            eff = Auto(),
                            usage = Auto(),
                            body = Let(
                              t = Redex(
                                t = Def(qn = qn"__unresolved__.plus") @ "plus",
                                elims = List(ETerm(v = Var(idx = 0)))
                              ) @ "plus a",
                              ty = Auto(),
                              eff = Auto(),
                              usage = Auto(),
                              body = Return(v = Var(idx = 0), usage = Auto())
                            )
                          ),
                          elims = List(ETerm(v = Var(idx = 0)))
                        ) @ "plus a b",
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Return(v = Var(idx = 0), usage = Auto())
                      )
                    )
                  ) @ """let b = getB
plus a b""",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε"
              ) @ "ε"
            ) @ "ε"
          ) @ "ε"
        ) @ """let a =
  let a1 = getA1
  let a2 = getA2
  plus a1 a2
let b = getB
plus a b""",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0), usage = Auto())
      ) @ "ε"
    ) @ "ε"
  ) @ "ε"
) @ "ε"