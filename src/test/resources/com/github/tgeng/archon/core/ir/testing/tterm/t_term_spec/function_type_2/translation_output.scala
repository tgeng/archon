FunctionType(
  binding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
    usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
  ) @ "a",
  bodyTy = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
    ) @ "b",
    bodyTy = F(
      vTy = Collapse(
        cTm = Redex(
          t = Redex(
            t = Def(qn = qn"__unresolved__.C") @ "C",
            elims = List(
              ETerm(
                v = Collapse(cTm = Return(v = Var(idx = 5) @ "a", usage = Auto() @ "ε") @ "a") @ "ε"
              )
            )
          ) @ "C a",
          elims = List(
            ETerm(v = Collapse(cTm = Return(v = Var(idx = 0) @ "b", usage = Auto()) @ "b") @ "ε")
          )
        ) @ "C a b"
      ) @ "ε",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
      usage = Collapse(cTm = Return(v = Auto(), usage = Auto()) @ "ε") @ "ε"
    ) @ "<> C a b",
    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
  ) @ "b : B -> <> C a b",
  effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
) @ "a : A -> b : B -> <> C a b"