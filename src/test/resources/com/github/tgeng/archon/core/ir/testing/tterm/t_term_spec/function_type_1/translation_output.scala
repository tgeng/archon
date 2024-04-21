Let(
  t = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
    ) @ "_",
    bodyTy = Let(
      t = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
        ) @ "_",
        bodyTy = Let(
          t = F(
            vTy = Collapse(cTm = Def(qn = qn"__unresolved__.C") @ "C") @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
            usage = Auto() @ "ε"
          ) @ "<> C",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "B -> <> C",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
  ) @ "A -> B -> <> C",
  ty = Auto(),
  eff = Auto(),
  usage = Auto(),
  body = Return(v = Var(idx = 0), usage = Auto())
) @ "ε"