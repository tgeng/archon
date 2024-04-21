List(
  PreData(
    qn = qn"test.Eq",
    tParamTys = List(
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Level") @ "Level",
          usage = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε"
        ) @ "l",
        INVARIANT
      ),
      (
        Binding(
          ty = Let(
            t = Def(qn = qn"__unresolved__.l") @ "l",
            ty = Auto() @ "ε",
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Redex(
                t = Def(qn = qn"__unresolved__.Type") @ "Type",
                elims = List(ETerm(v = Var(idx = 0) @ "ε"))
              ) @ "Type l",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
            ) @ "ε"
          ) @ "ε",
          usage = Def(qn = qn"archon.builtin.type.Usage.any")
        ) @ "A",
        INVARIANT
      ),
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.A") @ "A",
          usage = Def(qn = qn"archon.builtin.type.Usage.any")
        ) @ "x",
        INVARIANT
      )
    ),
    ty = Let(
      t = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any")) @ "ε"
        ) @ "_",
        bodyTy = Let(
          t = F(
            vTy = Collapse(
              cTm = Let(
                t = Redex(
                  t = Def(qn = qn"__unresolved__.Type") @ "Type",
                  elims = List(
                    ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l") @ "ε")
                  )
                ) @ "Type l",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε") @ "ε"
          ) @ "Type l",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "A -> Type l",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    constructors = List(
      PreConstructor(
        name = n"Refl",
        ty = Let(
          t = F(
            vTy = Collapse(
              cTm = Let(
                t = Redex(
                  t = Let(
                    t = Redex(
                      t = Let(
                        t = Redex(
                          t = Let(
                            t = Redex(
                              t = Def(qn = qn"__unresolved__.Eq") @ "Eq",
                              elims = List(
                                ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l"))
                              )
                            ) @ "Eq l",
                            ty = Auto(),
                            eff = Auto(),
                            usage = Auto(),
                            body = Return(v = Var(idx = 0), usage = Auto())
                          ) @ "ε",
                          elims = List(
                            ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A"))
                          )
                        ) @ "Eq l A",
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Return(v = Var(idx = 0), usage = Auto())
                      ) @ "ε",
                      elims = List(
                        ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.x") @ "x") @ "ε")
                      )
                    ) @ "Eq l A x",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Return(v = Var(idx = 0), usage = Auto())
                  ) @ "ε",
                  elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.x") @ "x")))
                ) @ "Eq l A x x",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
          ) @ "Eq l A x x",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      )
    )
  )
)