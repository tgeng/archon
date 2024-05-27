FunctionType(
  binding = Binding(
    ty = Collapse(cTm = Def(qn = qn"__unresolved__.A") @ "A") @ "ε",
    usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
  ) @ "_",
  bodyTy = FunctionType(
    binding = Binding(
      ty = Collapse(cTm = Def(qn = qn"__unresolved__.B") @ "B") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any"))
    ) @ "_",
    bodyTy = F(
      vTy = Collapse(cTm = Def(qn = qn"__unresolved__.C") @ "C") @ "ε",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
      usage = Collapse(cTm = Return(v = Auto() @ "ε", usage = Auto()) @ "ε") @ "ε"
    ) @ "<> C",
    effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
  ) @ "B -> <> C",
  effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
) @ "A -> B -> <> C"