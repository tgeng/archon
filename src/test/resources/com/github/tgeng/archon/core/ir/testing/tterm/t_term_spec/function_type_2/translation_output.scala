FunctionType(
  binding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "A",
    usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
  ) @ "a",
  bodyTy = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "B",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
    ) @ "b",
    bodyTy = F(
      vTy = Collapse(
        cTm = Redex(
          t = Def(qn = qn"__unresolved__.C") @ "C",
          elims = List(ETerm(v = Var(idx = 1) @ "a"), ETerm(v = Var(idx = 0) @ "b"))
        ) @ "C a b"
      ) @ "C a b",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
      usage = Auto() @ "ε"
    ) @ "<> C a b",
    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
    escapeStatus = EsLocal
  ) @ "b : B -> <> C a b",
  effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
  escapeStatus = EsLocal
) @ "a : A -> b : B -> <> C a b"