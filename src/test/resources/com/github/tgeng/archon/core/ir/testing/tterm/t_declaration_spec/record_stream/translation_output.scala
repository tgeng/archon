List(
  PreRecord(
    qn = qn"test.CStream",
    tParamTys = List(),
    ty = Let(
      t = Def(qn = qn"__unresolved__.l") @ "l",
      tBinding = Binding(ty = Auto() @ "ε", usage = Auto()) @ "$v",
      eff = Auto(),
      body = Redex(
        t = Def(qn = qn"__unresolved__.CType") @ "CType",
        elims = List(ETerm(v = Var(idx = 0) @ "ε"))
      ) @ "CType l"
    ) @ "ε",
    fields = List(
      Field(name = n"head", ty = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
      Field(
        name = n"tail",
        ty = FunctionType(
          binding = Binding(
            ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
          ) @ "m",
          bodyTy = FunctionType(
            binding = Binding(
              ty = Collapse(
                cTm = Redex(
                  t = Redex(
                    t = Redex(
                      t = Def(qn = qn"__unresolved__.Eq") @ "Eq",
                      elims = List(
                        ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"))
                      )
                    ) @ "Eq Nat",
                    elims = List(
                      ETerm(
                        v = Collapse(cTm = Return(v = Var(idx = 2) @ "m", usage = Auto()) @ "m") @ "ε"
                      )
                    )
                  ) @ "Eq Nat m",
                  elims = List(
                    ETerm(
                      v = Collapse(
                        cTm = Redex(
                          t = Def(qn = qn"__unresolved__.head") @ "head",
                          elims = List(
                            ETerm(
                              v = Collapse(cTm = Def(qn = qn"__unresolved__.self") @ "self") @ "ε"
                            )
                          )
                        ) @ "head self"
                      ) @ "ε"
                    )
                  )
                ) @ "Eq Nat m (head self"
              ) @ "ε",
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
            ) @ "_",
            bodyTy = Def(qn = qn"__unresolved__.CStream") @ "CStream",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε"
          ) @ "Eq Nat m (head self) -> CStream",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
        ) @ "m: Nat -> Eq Nat m (head self) -> CStream"
      )
    ),
    selfName = n"self"
  )
)