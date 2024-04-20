Let(
  t = Def(qn = qn"__unresolved__.effA") @ "effA",
  ty = Auto() @ "ε",
  eff = Auto(),
  usage = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.A") @ "A",
    ty = Auto(),
    eff = Auto(),
    usage = Auto(),
    body = Let(
      t = Def(qn = qn"__unresolved__.uA") @ "uA",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = FunctionType(
          binding = Binding(ty = Var(idx = 0) @ "ε", usage = Var(idx = 0)) @ "a",
          bodyTy = Let(
            t = Def(qn = qn"__unresolved__.effB") @ "effB",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Def(qn = qn"__unresolved__.B") @ "B",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = Def(qn = qn"__unresolved__.uB") @ "uB",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Let(
                  t = FunctionType(
                    binding = Binding(ty = Var(idx = 0), usage = Var(idx = 0)) @ "b",
                    bodyTy = Let(
                      t = Let(
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
                                  t = Def(qn = qn"__unresolved__.C") @ "C",
                                  elims = List(ETerm(v = Var(idx = 0)))
                                ) @ "C a",
                                ty = Auto(),
                                eff = Auto(),
                                usage = Auto(),
                                body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
                              ) @ "ε"
                            ) @ "ε",
                            elims = List(ETerm(v = Var(idx = 0)))
                          ) @ "C a b",
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
                        t = Def(qn = qn"__unresolved__.effC") @ "effC",
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Let(
                          t = Def(qn = qn"__unresolved__.uC") @ "uC",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Let(
                            t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Var(idx = 0)) @ "<effC> [uC] C a b",
                            ty = Auto(),
                            eff = Auto(),
                            usage = Auto(),
                            body = Return(v = Var(idx = 0), usage = Auto())
                          ) @ "ε"
                        ) @ "ε"
                      ) @ "ε"
                    ) @ "ε",
                    effects = Var(idx = 0)
                  ) @ "b: [uB] B -> <effC> [uC] C a b",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε"
              ) @ "ε"
            ) @ "ε"
          ) @ "ε",
          effects = Var(idx = 0)
        ) @ "a: [uA] A -> <effB> b: [uB] B -> <effC> [uC] C a b",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0), usage = Auto())
      ) @ "ε"
    ) @ "ε"
  ) @ "ε"
) @ "ε"