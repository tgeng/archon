List(
  PreData(
    qn = qn"test.Vec",
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
            body = Redex(
              t = Def(qn = qn"__unresolved__.Type") @ "Type",
              elims = List(ETerm(v = Var(idx = 0) @ "ε"))
            ) @ "Type l"
          ) @ "ε",
          usage = Def(qn = qn"archon.builtin.type.Usage.any")
        ) @ "t",
        COVARIANT
      )
    ),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any")) @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(
          cTm = Redex(
            t = Def(qn = qn"__unresolved__.Type") @ "Type",
            elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l") @ "ε"))
          ) @ "Type l"
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε") @ "ε"
      ) @ "Type l",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "Nat -> Type l",
    constructors = List(
      PreConstructor(
        name = n"Nil",
        ty = F(
          vTy = Collapse(
            cTm = Redex(
              t = Redex(
                t = Redex(
                  t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                  elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l")))
                ) @ "Vec l",
                elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t") @ "ε"))
              ) @ "Vec l t",
              elims = List(
                ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.Zero") @ "Zero") @ "ε")
              )
            ) @ "Vec l t Zero"
          ) @ "ε",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
        ) @ "Vec l t Zero"
      ),
      PreConstructor(
        name = n"Succ",
        ty = FunctionType(
          binding = Binding(
            ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
          ) @ "n",
          bodyTy = FunctionType(
            binding = Binding(
              ty = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t"),
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
            ) @ "_",
            bodyTy = FunctionType(
              binding = Binding(
                ty = Collapse(
                  cTm = Redex(
                    t = Redex(
                      t = Redex(
                        t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                        elims = List(
                          ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l"))
                        )
                      ) @ "Vec l",
                      elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t")))
                    ) @ "Vec l t",
                    elims = List(
                      ETerm(
                        v = Collapse(cTm = Return(v = Var(idx = 5) @ "n", usage = Auto()) @ "n") @ "ε"
                      )
                    )
                  ) @ "Vec l t n"
                ) @ "ε",
                usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
              ) @ "_",
              bodyTy = F(
                vTy = Collapse(
                  cTm = Redex(
                    t = Redex(
                      t = Redex(
                        t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                        elims = List(
                          ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l"))
                        )
                      ) @ "Vec l",
                      elims = List(ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t")))
                    ) @ "Vec l t",
                    elims = List(
                      ETerm(
                        v = Collapse(
                          cTm = Redex(
                            t = Def(qn = qn"__unresolved__.Succ") @ "Succ",
                            elims = List(
                              ETerm(
                                v = Collapse(
                                  cTm = Return(v = Var(idx = 8) @ "n", usage = Auto()) @ "n"
                                ) @ "ε"
                              )
                            )
                          ) @ "Succ n"
                        ) @ "ε"
                      )
                    )
                  ) @ "Vec l t (Succ n"
                ) @ "ε",
                effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
                usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
              ) @ "Vec l t (Succ n",
              effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
            ) @ "Vec l t n -> Vec l t (Succ n",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
          ) @ "t -> Vec l t n -> Vec l t (Succ n",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
        ) @ "n: Nat -> t -> Vec l t n -> Vec l t (Succ n"
      )
    )
  )
)