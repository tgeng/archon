List(
  TData(
    name = "Nat",
    tParamTys = List(),
    ty = TF(
      ty = TRedex(
        c = TId(id = "Type") @ "Type",
        elims = List(ETerm(v = TLevelLiteral(level = 0) @ "0L"))
      ) @ "Type 0L",
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TDef(qn = qn"archon.builtin.type.Usage.u1") @ "ε"
    ) @ "Type 0L",
    constructors = List(
      TConstructor(
        name = "Zero",
        ty = TF(
          ty = TId(id = "Nat") @ "Nat",
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.u1")
        ) @ "Nat"
      ),
      TConstructor(
        name = "Succ",
        ty = TFunctionType(
          arg = TBinding(
            name = "_",
            ty = TId(id = "Nat"),
            usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
          ),
          bodyType = TF(
            ty = TId(id = "Nat"),
            effects = TDef(qn = qn"archon.builtin.effects.total"),
            usage = TDef(qn = qn"archon.builtin.type.Usage.u1")
          ),
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          escapeStatus = EsUnknown
        ) @ "Nat -> Nat"
      )
    )
  ),
  TDefinition(
    name = "prec",
    tParamTys = List(),
    ty = TFunctionType(
      arg = TBinding(
        name = "_",
        ty = TId(id = "Nat"),
        usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
      ),
      bodyType = TF(
        ty = TId(id = "Nat"),
        effects = TDef(qn = qn"archon.builtin.effects.total"),
        usage = TAuto() @ "ε"
      ) @ "<> Nat",
      effects = TDef(qn = qn"archon.builtin.effects.total"),
      escapeStatus = EsUnknown
    ) @ "Nat -> <> Nat",
    clauses = List(
      TClause(
        patterns = List(TcPattern(pattern = TpId(name = "Zero"))),
        body = Some(value = TId(id = "Zero") @ "Zero")
      ),
      TClause(
        patterns = List(
          TcPattern(
            pattern = TpXConstructor(forced = false, name = "Succ", args = List(TpId(name = "m")))
          )
        ),
        body = Some(value = TId(id = "m") @ "m")
      )
    )
  )
)