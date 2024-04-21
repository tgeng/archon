Let(
  t = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
    ) @ "a",
    bodyTy = Let(
      t = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
        ) @ "b",
        bodyTy = Let(
          t = F(
            vTy = Collapse(
              cTm = Let(
                t = Redex(
                  t = Let(
                    t = Redex(
                      t = Def(qn = qn"__unresolved__.C") @ "C",
                      elims = List(ETerm(v = Var(idx = 5) @ "a"))
                    ) @ "C a",
                    ty = Auto() @ "ε",
                    eff = Auto(),
                    usage = Auto(),
                    body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
                  ) @ "ε",
                  elims = List(ETerm(v = Var(idx = 0) @ "b"))
                ) @ "C a b",
                ty = Auto(),
                eff = Auto(),
                usage = Auto(),
                body = Return(v = Var(idx = 0), usage = Auto())
              ) @ "ε"
            ) @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
            usage = Auto()
          ) @ "<> C a b",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "b : B -> <> C a b",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
  ) @ "a : A -> b : B -> <> C a b",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Return(v = Var(idx = 0), usage = Auto())
) @ "ε"