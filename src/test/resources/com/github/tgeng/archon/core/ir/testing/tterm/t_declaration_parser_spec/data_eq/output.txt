TData(
  name = "Eq",
  tParamTys = List(
    (
      TBinding(
        name = "l",
        ty = TId(id = "Level") @ "Level",
        usage = TDef(qn = qn"archon.builtin.type.Usage.any") @ "ε"
      ),
      INVARIANT
    ),
    (
      TBinding(
        name = "A",
        ty = TApp(f = TId(id = "Type") @ "Type", arg = TId(id = "l") @ "l") @ "Type l",
        usage = TDef(qn = qn"archon.builtin.type.Usage.any")
      ),
      INVARIANT
    ),
    (
      TBinding(
        name = "x",
        ty = TId(id = "A") @ "A",
        usage = TDef(qn = qn"archon.builtin.type.Usage.any")
      ),
      INVARIANT
    )
  ),
  ty = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TId(id = "A"),
      usage = TDef(qn = qn"archon.builtin.type.Usage.any")
    ),
    bodyType = TF(
      ty = TApp(f = TId(id = "Type"), arg = TId(id = "l")),
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TDef(qn = qn"archon.builtin.type.Usage.one") @ "ε"
    ) @ "Type l",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ "A -> Type l",
  constructors = List(
    TConstructor(
      name = "Refl",
      ty = TF(
        ty = TApp(
          f = TApp(
            f = TApp(
              f = TApp(f = TId(id = "Eq") @ "Eq", arg = TId(id = "l")) @ "Eq l",
              arg = TId(id = "A")
            ) @ "Eq l A",
            arg = TId(id = "x") @ "x"
          ) @ "Eq l A x",
          arg = TId(id = "x")
        ) @ "Eq l A x x",
        effects = TDef(qn = qn"archon.builtin.effects.total"),
        usage = TDef(qn = qn"archon.builtin.type.Usage.one")
      ) @ "Eq l A x x"
    )
  )
)