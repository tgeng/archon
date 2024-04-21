List(
  PreData(
    qn = qn"test.Nat",
    tParamTys = List(),
    ty = Let(
      t = Let(
        t = Redex(
          t = Def(qn = qn"__unresolved__.Type") @ "Type",
          elims = List(
            ETerm(v = Level(literal = LevelOrder(m = 0, n = 0), maxOperands = SeqMap()) @ "0L")
          )
        ) @ "Type 0L",
        ty = Auto() @ "ε",
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
      ) @ "ε",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = Def(qn = qn"archon.builtin.effects.total") @ "ε",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Let(
          t = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Var(idx = 0)) @ "Type 0L",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Return(v = Var(idx = 0), usage = Auto())
          ) @ "ε"
        ) @ "ε"
      ) @ "ε"
    ) @ "ε",
    constructors = List(
      PreConstructor(
        name = n"Zero",
        ty = Let(
          t = Def(qn = qn"__unresolved__.Nat") @ "Nat",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = Def(qn = qn"archon.builtin.effects.total"),
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Def(qn = qn"archon.builtin.type.Usage.one"),
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Var(idx = 0)) @ "Nat",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              )
            )
          )
        ) @ "ε"
      ),
      PreConstructor(
        name = n"Succ",
        ty = Let(
          t = Def(qn = qn"archon.builtin.effects.total"),
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = Def(qn = qn"__unresolved__.Nat") @ "Nat",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = FunctionType(
                  binding = Binding(ty = Var(idx = 0), usage = Var(idx = 0)) @ "_",
                  bodyTy = Let(
                    t = Def(qn = qn"__unresolved__.Nat") @ "Nat",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Let(
                      t = Def(qn = qn"archon.builtin.effects.total"),
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Let(
                        t = Def(qn = qn"archon.builtin.type.Usage.one"),
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Let(
                          t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Var(idx = 0)) @ "Nat",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto())
                        )
                      )
                    )
                  ),
                  effects = Var(idx = 0)
                ) @ "Nat -> Nat",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε"
          ) @ "ε"
        ) @ "ε"
      )
    )
  )
)