List(
  TData(
    name = "Eq",
    tParamTys = List(
      (
        TBinding(
          name = "l",
          ty = TId(id = "Level") @ "Level",
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
        ),
        INVARIANT
      ),
      (
        TBinding(
          name = "A",
          ty = TRedex(c = TId(id = "Type") @ "Type", elims = List(ETerm(v = TId(id = "l") @ "l"))) @ "Type l",
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
        ),
        INVARIANT
      ),
      (
        TBinding(
          name = "x",
          ty = TId(id = "A") @ "A",
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
        ),
        INVARIANT
      )
    ),
    ty = TFunctionType(
      arg = TBinding(
        name = "_",
        ty = TId(id = "A"),
        usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
      ),
      bodyType = TF(
        ty = TRedex(c = TId(id = "Type"), elims = List(ETerm(v = TId(id = "l")))),
        effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
        usage = TDef(qn = qn"archon.builtin.type.Usage.u1") @ "ε"
      ) @ "Type l",
      effects = TDef(qn = qn"archon.builtin.effects.total"),
      escapeStatus = EsUnknown
    ) @ "A -> Type l",
    constructors = List(
      TConstructor(
        name = "Refl",
        ty = TF(
          ty = TRedex(
            c = TId(id = "Eq") @ "Eq",
            elims = List(
              ETerm(v = TId(id = "l")),
              ETerm(v = TId(id = "A")),
              ETerm(v = TId(id = "x") @ "x"),
              ETerm(v = TId(id = "x"))
            )
          ) @ "Eq l A x x",
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.u1")
        ) @ "Eq l A x x"
      )
    )
  )
)