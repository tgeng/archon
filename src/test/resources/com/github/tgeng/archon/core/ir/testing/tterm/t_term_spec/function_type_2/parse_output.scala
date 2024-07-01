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
      ty = TRedex(
        c = TId(id = "C") @ "C",
        elims = List(ETerm(v = TId(id = "a") @ "a"), ETerm(v = TId(id = "b") @ "b"))
      ) @ "C a b",
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TAuto() @ "ε"
    ) @ "<> C a b",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ "b : B -> <> C a b",
  effects = TDef(qn = qn"archon.builtin.effects.total")
) @ "a : A -> b : B -> <> C a b"