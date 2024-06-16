TFunctionType(
  arg = TBinding(
    name = "a",
    ty = TId(id = "A") @ "A",
    usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
  ),
  bodyType = TFunctionType(
    arg = TBinding(
      name = "b",
      ty = TId(id = "B") @ "B",
      usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
    ),
    bodyType = TF(
      ty = TApp(
        f = TApp(f = TId(id = "C") @ "C", arg = TId(id = "a") @ "a") @ "C a",
        arg = TId(id = "b") @ "b"
      ) @ "C a b",
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TAuto() @ "ε"
    ) @ "<> C a b",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ "b : B -> <> C a b",
  effects = TDef(qn = qn"archon.builtin.effects.total")
) @ "a : A -> b : B -> <> C a b"