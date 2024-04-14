TData(
  name = "Nat",
  tParamTys = List(),
  ty = TF(
    ty = TApp(f = TId(id = "Type") @ "Type", arg = TLevelLiteral(level = 0) @ "0L") @ "Type 0L",
    effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
    usage = TDef(qn = qn"archon.builtin.type.Usage.one") @ "ε"
  ) @ "Type 0L",
  constructors = List(
    TConstructor(
      name = "Zero",
      ty = TF(
        ty = TId(id = "Nat") @ "Nat",
        effects = TDef(qn = qn"archon.builtin.effects.total"),
        usage = TDef(qn = qn"archon.builtin.type.Usage.one")
      ) @ "Nat"
    ),
    TConstructor(
      name = "Succ",
      ty = TFunctionType(
        arg = TBinding(
          name = "_",
          ty = TId(id = "Nat"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.any") @ "ε"
        ),
        bodyType = TF(
          ty = TId(id = "Nat"),
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.one")
        ),
        effects = TDef(qn = qn"archon.builtin.effects.total")
      ) @ "Nat -> Nat"
    )
  )
)