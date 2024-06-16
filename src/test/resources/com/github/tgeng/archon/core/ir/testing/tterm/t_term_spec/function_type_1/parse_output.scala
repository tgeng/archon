TFunctionType(
  arg = TBinding(
    name = "_",
    ty = TId(id = "A") @ "A",
    usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
  ),
  bodyType = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TId(id = "B") @ "B",
      usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
    ),
    bodyType = TF(
      ty = TId(id = "C") @ "C",
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TAuto() @ "ε"
    ) @ "<> C",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ "B -> <> C",
  effects = TDef(qn = qn"archon.builtin.effects.total")
) @ "A -> B -> <> C"