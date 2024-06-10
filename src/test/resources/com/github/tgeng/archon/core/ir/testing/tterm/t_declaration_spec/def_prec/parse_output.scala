TDefinition(
  name = "prec",
  tParamTys = List(),
  ty = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TDef(qn = qn"test.Nat") @ ".test.Nat",
      usage = TDef(qn = qn"archon.builtin.type.Usage.any") @ "ε"
    ),
    bodyType = TF(
      ty = TDef(qn = qn"test.Nat"),
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TAuto() @ "ε"
    ) @ "<> .test.Nat",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ ".test.Nat -> <> .test.Nat",
  clauses = List(
    TClause(
      patterns = List(
        TcPattern(pattern = TpXConstructor(forced = false, name = "Zero", args = List()))
      ),
      body = Some(value = TDef(qn = qn"test.Nat.Zero") @ ".test.Nat.Zero")
    ),
    TClause(
      patterns = List(
        TcPattern(
          pattern = TpXConstructor(forced = false, name = "Succ", args = List(TpVar(name = "m")))
        )
      ),
      body = Some(value = TId(id = "m") @ "m")
    )
  )
)