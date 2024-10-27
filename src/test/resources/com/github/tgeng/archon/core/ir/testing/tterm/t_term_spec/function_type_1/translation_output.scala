FunctionType(
  binding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "A",
    usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
  ) @ "_",
  bodyTy = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "B",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
    ) @ "_",
    bodyTy = F(
      vTy = Collapse(cTm = Def(qn = qn"__unresolved__.C") @ "C") @ "C",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
      usage = Auto() @ "ε"
    ) @ "<> C",
    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
    escapeStatus = EsLocal
  ) @ "B -> <> C",
  effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
  escapeStatus = EsLocal
) @ "A -> B -> <> C"