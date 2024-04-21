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
          t = Def(qn = qn"archon.builtin.type.Usage.any"),
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Let(
            t = FunctionType(
              binding = Binding(ty = Var(idx = 0), usage = Var(idx = 0)) @ "_",
              bodyTy = Let(
                t = Let(
                  t = Def(qn = qn"__unresolved__.l") @ "l",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Let(
                    t = Redex(
                      t = Def(qn = qn"__unresolved__.Type") @ "Type",
                      elims = List(ETerm(v = Var(idx = 0)))
                    ) @ "Type l",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Return(v = Var(idx = 0), usage = Auto())
                  )
                ),
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Let(
                  t = Def(qn = qn"archon.builtin.effects.total"),
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Let(
                    t = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Let(
                      t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Var(idx = 0)) @ "Type l",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Return(v = Var(idx = 0), usage = Auto())
                    ) @ "ε"
                  ) @ "ε"
                ) @ "ε"
              ) @ "ε",
              effects = Var(idx = 0)
            ) @ "Nat -> Type l",
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
        name = n"Nil",
        ty = Let(
          t = Let(
            t = Def(qn = qn"__unresolved__.Zero") @ "Zero",
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Redex(
                t = Let(
                  t = Def(qn = qn"__unresolved__.t") @ "t",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Let(
                    t = Redex(
                      t = Let(
                        t = Def(qn = qn"__unresolved__.l") @ "l",
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Let(
                          t = Redex(
                            t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                            elims = List(ETerm(v = Var(idx = 0)))
                          ) @ "Vec l",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto())
                        ) @ "ε"
                      ) @ "ε",
                      elims = List(ETerm(v = Var(idx = 0)))
                    ) @ "Vec l t",
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Return(v = Var(idx = 0), usage = Auto())
                  ) @ "ε"
                ) @ "ε",
                elims = List(ETerm(v = Var(idx = 0)))
              ) @ "Vec l t Zero",
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
                t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Var(idx = 0)) @ "Vec l t Zero",
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
              t = Def(qn = qn"archon.builtin.type.Usage.any"),
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Let(
                t = FunctionType(
                  binding = Binding(ty = Var(idx = 0), usage = Var(idx = 0)) @ "n",
                  bodyTy = Let(
                    t = Def(qn = qn"archon.builtin.effects.total"),
                    ty = Auto(),
                    eff = Auto(),
                    usage = Auto(),
                    body = Let(
                      t = Def(qn = qn"__unresolved__.t") @ "t",
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
                            bodyTy = Let(
                              t = Def(qn = qn"archon.builtin.effects.total"),
                              ty = Auto(),
                              eff = Auto(),
                              usage = Auto(),
                              body = Let(
                                t = Let(
                                  t = Redex(
                                    t = Let(
                                      t = Def(qn = qn"__unresolved__.t") @ "t",
                                      ty = Auto(),
                                      eff = Auto(),
                                      usage = Auto(),
                                      body = Let(
                                        t = Redex(
                                          t = Let(
                                            t = Def(qn = qn"__unresolved__.l") @ "l",
                                            ty = Auto(),
                                            eff = Auto(),
                                            usage = Auto(),
                                            body = Let(
                                              t = Redex(
                                                t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                                                elims = List(ETerm(v = Var(idx = 0)))
                                              ) @ "Vec l",
                                              ty = Auto(),
                                              eff = Auto(),
                                              usage = Auto(),
                                              body = Return(v = Var(idx = 0), usage = Auto())
                                            )
                                          ),
                                          elims = List(ETerm(v = Var(idx = 0)))
                                        ) @ "Vec l t",
                                        ty = Auto(),
                                        eff = Auto(),
                                        usage = Auto(),
                                        body = Return(v = Var(idx = 0), usage = Auto())
                                      )
                                    ),
                                    elims = List(ETerm(v = Var(idx = 5) @ "n"))
                                  ) @ "Vec l t n",
                                  ty = Auto(),
                                  eff = Auto(),
                                  usage = Auto(),
                                  body = Return(v = Var(idx = 0), usage = Auto())
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
                                      bodyTy = Let(
                                        t = Let(
                                          t = Let(
                                            t = Redex(
                                              t = Def(qn = qn"__unresolved__.Succ") @ "Succ",
                                              elims = List(ETerm(v = Var(idx = 8) @ "n"))
                                            ) @ "Succ n",
                                            ty = Auto(),
                                            eff = Auto(),
                                            usage = Auto(),
                                            body = Return(v = Var(idx = 0), usage = Auto())
                                          ) @ "ε",
                                          ty = Auto(),
                                          eff = Auto(),
                                          usage = Auto(),
                                          body = Let(
                                            t = Redex(
                                              t = Let(
                                                t = Def(qn = qn"__unresolved__.t") @ "t",
                                                ty = Auto(),
                                                eff = Auto(),
                                                usage = Auto(),
                                                body = Let(
                                                  t = Redex(
                                                    t = Let(
                                                      t = Def(qn = qn"__unresolved__.l") @ "l",
                                                      ty = Auto(),
                                                      eff = Auto(),
                                                      usage = Auto(),
                                                      body = Let(
                                                        t = Redex(
                                                          t = Def(qn = qn"__unresolved__.Vec") @ "Vec",
                                                          elims = List(ETerm(v = Var(idx = 0)))
                                                        ) @ "Vec l",
                                                        ty = Auto(),
                                                        eff = Auto(),
                                                        usage = Auto(),
                                                        body = Return(
                                                          v = Var(idx = 0),
                                                          usage = Auto()
                                                        )
                                                      )
                                                    ),
                                                    elims = List(ETerm(v = Var(idx = 0)))
                                                  ) @ "Vec l t",
                                                  ty = Auto(),
                                                  eff = Auto(),
                                                  usage = Auto(),
                                                  body = Return(v = Var(idx = 0), usage = Auto())
                                                )
                                              ),
                                              elims = List(ETerm(v = Var(idx = 0)))
                                            ) @ "Vec l t (Succ n",
                                            ty = Auto(),
                                            eff = Auto(),
                                            usage = Auto(),
                                            body = Return(v = Var(idx = 0), usage = Auto())
                                          )
                                        ) @ "ε",
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
                                              t = F(
                                                vTy = Var(idx = 0),
                                                effects = Var(idx = 0),
                                                usage = Var(idx = 0)
                                              ) @ "Vec l t (Succ n",
                                              ty = Auto(),
                                              eff = Auto(),
                                              usage = Auto(),
                                              body = Return(v = Var(idx = 0), usage = Auto())
                                            )
                                          )
                                        )
                                      ) @ "ε",
                                      effects = Var(idx = 0)
                                    ) @ "Vec l t n -> Vec l t (Succ n",
                                    ty = Auto(),
                                    eff = Auto(),
                                    usage = Auto(),
                                    body = Return(v = Var(idx = 0), usage = Auto())
                                  ) @ "ε"
                                ) @ "ε"
                              ) @ "ε"
                            ) @ "ε",
                            effects = Var(idx = 0)
                          ) @ "t -> Vec l t n -> Vec l t (Succ n",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto())
                        ) @ "ε"
                      ) @ "ε"
                    ) @ "ε"
                  ) @ "ε",
                  effects = Var(idx = 0)
                ) @ "n: Nat -> t -> Vec l t n -> Vec l t (Succ n",
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