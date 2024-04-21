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
        ) @ "t",
        COVARIANT
      )
    ),
    ty = Let(
      t = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
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
      ) @ "Nat -> Type l",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    constructors = List(
      PreConstructor(
        name = n"Nil",
        ty = Let(
          t = F(
            vTy = Collapse(
              cTm = Let(
                t = Redex(
                  t = Let(
                    t = Redex(
                      t = Let(
                        t = Redex(
                          t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                          elims = List(
                            ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l"))
                          )
                        ) @ "Vec l",
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Return(v = Var(idx = 0), usage = Auto())
                      ) @ "ε",
                      elims = List(
                        ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t") @ "ε")
                      )
                    ) @ "Vec l t",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Return(v = Var(idx = 0), usage = Auto())
                  ) @ "ε",
                  elims = List(
                    ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.Zero") @ "Zero") @ "ε")
                  )
                ) @ "Vec l t Zero",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
          ) @ "Vec l t Zero",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      ),
      PreConstructor(
        name = n"Succ",
        ty = Let(
          t = FunctionType(
            binding = Binding(
              ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
            ) @ "n",
            bodyTy = Let(
              t = FunctionType(
                binding = Binding(
                  ty = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t"),
                  usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
                ) @ "_",
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
                                    t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                                    elims = List(
                                      ETerm(
                                        v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l")
                                      )
                                    )
                                  ) @ "Vec l",
                                  ty = Auto(),
                                  eff = Auto(),
                                  usage = Auto(),
                                  body = Return(v = Var(idx = 0), usage = Auto())
                                ),
                                elims = List(
                                  ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t"))
                                )
                              ) @ "Vec l t",
                              ty = Auto(),
                              eff = Auto(),
                              usage = Auto(),
                              body = Return(v = Var(idx = 0), usage = Auto())
                            ),
                            elims = List(ETerm(v = Var(idx = 5) @ "n"))
                          ) @ "Vec l t n",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto())
                        ) @ "ε"
                      ) @ "ε",
                      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
                    ) @ "_",
                    bodyTy = Let(
                      t = F(
                        vTy = Collapse(
                          cTm = Let(
                            t = Redex(
                              t = Let(
                                t = Redex(
                                  t = Let(
                                    t = Redex(
                                      t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                                      elims = List(
                                        ETerm(
                                          v = Collapse(cTm = Def(qn = qn"__unresolved__.l") @ "l")
                                        )
                                      )
                                    ) @ "Vec l",
                                    ty = Auto(),
                                    eff = Auto(),
                                    usage = Auto(),
                                    body = Return(v = Var(idx = 0), usage = Auto())
                                  ),
                                  elims = List(
                                    ETerm(v = Collapse(cTm = Def(qn = qn"__unresolved__.t") @ "t"))
                                  )
                                ) @ "Vec l t",
                                ty = Auto(),
                                eff = Auto(),
                                usage = Auto(),
                                body = Return(v = Var(idx = 0), usage = Auto())
                              ),
                              elims = List(
                                ETerm(
                                  v = Collapse(
                                    cTm = Let(
                                      t = Redex(
                                        t = Def(qn = qn"__unresolved__.Succ") @ "Succ",
                                        elims = List(ETerm(v = Var(idx = 8) @ "n"))
                                      ) @ "Succ n",
                                      ty = Auto(),
                                      eff = Auto(),
                                      usage = Auto(),
                                      body = Return(v = Var(idx = 0), usage = Auto())
                                    ) @ "ε"
                                  ) @ "ε"
                                )
                              )
                            ) @ "Vec l t (Succ n",
                            ty = Auto(),
                            eff = Auto(),
                            usage = Auto(),
                            body = Return(v = Var(idx = 0), usage = Auto())
                          ) @ "ε"
                        ) @ "ε",
                        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
                        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
                      ) @ "Vec l t (Succ n",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Return(v = Var(idx = 0), usage = Auto())
                    ) @ "ε",
                    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
                  ) @ "Vec l t n -> Vec l t (Succ n",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε",
                effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
              ) @ "t -> Vec l t n -> Vec l t (Succ n",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ) @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
          ) @ "n: Nat -> t -> Vec l t n -> Vec l t (Succ n",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      )
    )
  )
)