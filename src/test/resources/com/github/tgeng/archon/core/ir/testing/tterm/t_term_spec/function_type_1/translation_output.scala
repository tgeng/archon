Let(
  t = Def(qn = qn"archon.builtin.effects.total") @ "ε",
  ty = Auto() @ "ε",
  eff = Auto(),
  usage = Auto(),
  body = Let(
    t = Def(qn = qn"__unresolved__.A") @ "A",
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
          binding = Binding(ty = Var(idx = 0) @ "ε", usage = Var(idx = 0)) @ "_",
          bodyTy = Let(
            t = Def(qn = qn"archon.builtin.effects.total"),
            ty = Auto(),
            eff = Auto(),
            usage = Auto(),
            body = Let(
              t = Def(qn = qn"__unresolved__.B") @ "B",
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
                      t = Def(qn = qn"__unresolved__.C") @ "C",
                      ty = Auto(),
                      eff = Auto(),
                      usage = Auto(),
                      body = Let(
                        t = Def(qn = qn"archon.builtin.effects.total"),
                        ty = Auto(),
                        eff = Auto(),
                        usage = Auto(),
                        body = Let(
                          t = F(vTy = Var(idx = 0), effects = Var(idx = 0), usage = Auto()) @ "<> C",
                          ty = Auto(),
                          eff = Auto(),
                          usage = Auto(),
                          body = Return(v = Var(idx = 0), usage = Auto()) @ "ε"
                        ) @ "ε"
                      ) @ "ε"
                    ) @ "ε",
                    effects = Var(idx = 0)
                  ) @ "B -> <> C",
                  ty = Auto(),
                  eff = Auto(),
                  usage = Auto(),
                  body = Return(v = Var(idx = 0), usage = Auto())
                ) @ "ε"
              ) @ "ε"
            ) @ "ε"
          ) @ "ε",
          effects = Var(idx = 0)
        ) @ "A -> B -> <> C",
        ty = Auto(),
        eff = Auto(),
        usage = Auto(),
        body = Return(v = Var(idx = 0), usage = Auto())
      ) @ "ε"
    ) @ "ε"
  ) @ "ε"
) @ "ε"