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
          t = FunctionType(
            binding = Binding(
              ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
            ) @ "m",
            bodyTy = Let(
              t = FunctionType(
                binding = Binding(
                  ty = Collapse(
                    cTm = Let(
                      t = Redex(
                        t = Let(
                          t = Redex(
                            t = Let(
                              t = Redex(
                                t = Def(qn = qn"__unresolved__.Eq") @ "Eq",
                                elims = List(
                                  ETerm(
                                    v = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat")
                                  )
                                )
                              ) @ "Eq Nat",
                              ty = Auto(),
                              eff = Auto(),
                              usage = Auto(),
                              body = Return(v = Var(idx = 0), usage = Auto())
                            ) @ "ε",
                            elims = List(ETerm(v = Var(idx = 2) @ "m"))
                          ) @ "Eq Nat m",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto())
                        ) @ "ε",
                        elims = List(
                          ETerm(
                            v = Collapse(
                              cTm = Let(
                                t = Redex(
                                  t = Def(qn = qn"__unresolved__.head") @ "head",
                                  elims = List(
                                    ETerm(
                                      v = Collapse(cTm = Def(qn = qn"__unresolved__.self") @ "self") @ "ε"
                                    )
                                  )
                                ) @ "head self",
                                ty = Auto(),
                                eff = Auto(),
                                usage = Auto(),
                                body = Return(v = Var(idx = 0), usage = Auto())
                              ) @ "ε"
                            ) @ "ε"
                          )
                        )
                      ) @ "Eq Nat m (head self",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Return(v = Var(idx = 0), usage = Auto())
                    ) @ "ε"
                  ) @ "ε",
                  usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
                ) @ "_",
                bodyTy = Def(qn = qn"__unresolved__.CStream") @ "CStream",
                effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε"
              ) @ "Eq Nat m (head self) -> CStream",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ) @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
          ) @ "m: Nat -> Eq Nat m (head self) -> CStream",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      )
    ),
    selfName = n"self"
  )
)