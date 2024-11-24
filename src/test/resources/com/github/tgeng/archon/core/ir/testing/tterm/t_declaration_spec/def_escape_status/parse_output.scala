List(
  TDefinition(
    name = "foo",
    tParamTys = List(
      (
        TBinding(
          name = "x",
          ty = TId(id = "Nat") @ "Nat",
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
        ),
        EsLocal
      ),
      (
        TBinding(
          name = "y",
          ty = TId(id = "Nat"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
        ),
        EsReturned
      ),
      (
        TBinding(
          name = "z",
          ty = TId(id = "Nat"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
        ),
        EsUnknown
      )
    ),
    ty = TFunctionType(
      arg = TBinding(
        name = "_",
        ty = TId(id = "Nat"),
        usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
      ),
      bodyType = TFunctionType(
        arg = TBinding(
          name = "_",
          ty = TId(id = "Nat"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
        ),
        bodyType = TFunctionType(
          arg = TBinding(
            name = "_",
            ty = TId(id = "Nat"),
            usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
          ),
          bodyType = TF(
            ty = TId(id = "Nat"),
            effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
            usage = TAuto() @ "ε"
          ) @ "<> Nat",
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          escapeStatus = EsUnknown
        ) @ "Nat -> <> Nat",
        effects = TDef(qn = qn"archon.builtin.effects.total"),
        escapeStatus = EsReturned
      ) @ "Nat -> esc Nat -> <> Nat",
      effects = TDef(qn = qn"archon.builtin.effects.total"),
      escapeStatus = EsLocal
    ) @ "Nat -> ret Nat -> esc Nat -> <> Nat",
    clauses = List(
      TClause(
        patterns = List(
          TcPattern(pattern = TpId(name = "a")),
          TcPattern(pattern = TpId(name = "b")),
          TcPattern(pattern = TpId(name = "c"))
        ),
        body = Some(value = TId(id = "b") @ "b")
      )
    )
  )
)