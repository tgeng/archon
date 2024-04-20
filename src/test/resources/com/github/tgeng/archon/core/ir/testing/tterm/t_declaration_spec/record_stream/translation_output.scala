List(
  PreRecord(
    qn = qn"test.CStream",
    tParamTys = List(),
    ty = Let(
      t = Def(qn = qn"__unresolved__.l") @ "l",
      ty = Auto() @ "ε",
      eff = Auto(),
      usage = Auto(),
      body = Let(
        t = Redex(
          t = Def(qn = qn"__unresolved__.CType") @ "CType",
          elims = List(ETerm(v = Var(idx = 0) @ "ε"))
        ) @ "CType l",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
      ) @ "ε"
    ) @ "ε",
    fields = List(
      Field(name = n"head", ty = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
      Field(
        name = n"tail",
        ty = Let(
          t = Def(qn = qn"archon.builtin.effects.total") @ "ε",
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
                  binding = Binding(ty = Var(idx = 0), usage = Var(idx = 0)) @ "m",
                  bodyTy = Let(
                    t = Def(qn = qn"archon.builtin.effects.total"),
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Let(
                      t = Let(
                        t = Let(
                          t = Def(qn = qn"__unresolved__.self") @ "self",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Let(
                            t = Redex(
                              t = Def(qn = qn"__unresolved__.head") @ "head",
                              elims = List(ETerm(v = Var(idx = 0)))
                            ) @ "head self",
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
                              t = Return(v = Var(idx = 2) @ "m", usage = Auto()) @ "m",
                              ty = Auto(),
                              eff = Auto(),
                              usage = Auto(),
                              body = Let(
                                t = Redex(
                                  t = Let(
                                    t = Def(qn = qn"__unresolved__.Nat") @ "Nat",
                                    ty = Auto(),
                                    eff = Auto(),
                                    usage = Auto(),
                                    body = Let(
                                      t = Redex(
                                        t = Def(qn = qn"__unresolved__.Eq") @ "Eq",
                                        elims = List(ETerm(v = Var(idx = 0)))
                                      ) @ "Eq Nat",
                                      ty = Auto(),
                                      eff = Auto(),
                                      usage = Auto(),
                                      body = Return(v = Var(idx = 0), usage = Auto())
                                    ) @ "ε"
                                  ) @ "ε",
                                  elims = List(ETerm(v = Var(idx = 0)))
                                ) @ "Eq Nat m",
                                ty = Auto(),
                                eff = Auto(),
                                usage = Auto(),
                                body = Return(v = Var(idx = 0), usage = Auto())
                              ) @ "ε"
                            ) @ "ε",
                            elims = List(ETerm(v = Var(idx = 0)))
                          ) @ "Eq Nat m (head self",
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
                        t = Def(qn = qn"archon.builtin.type.Usage.any"),
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Let(
                          t = FunctionType(
                            binding = Binding(ty = Var(idx = 0), usage = Var(idx = 0)) @ "_",
                            bodyTy = Def(qn = qn"__unresolved__.CStream") @ "CStream",
                            effects = Var(idx = 0)
                          ) @ "Eq Nat m (head self) -> CStream",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto())
                        ) @ "ε"
                      ) @ "ε"
                    ) @ "ε"
                  ) @ "ε",
                  effects = Var(idx = 0)
                ) @ "m: Nat -> Eq Nat m (head self) -> CStream",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε"
          ) @ "ε"
        ) @ "ε"
      )
    ),
    selfName = n"self"
  )
)