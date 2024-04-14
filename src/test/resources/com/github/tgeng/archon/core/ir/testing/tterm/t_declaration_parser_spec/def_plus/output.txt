TDefinition(
  name = "plus",
  tParamTys = List(),
  ty = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TId(id = "Nat") @ "Nat",
      usage = TDef(qn = qn"archon.builtin.type.Usage.any") @ "ε"
    ),
    bodyType = TFunctionType(
      arg = TBinding(
        name = "_",
        ty = TId(id = "Nat"),
        usage = TDef(qn = qn"archon.builtin.type.Usage.any")
      ),
      bodyType = TF(
        ty = TId(id = "Nat"),
        effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
        usage = TAuto() @ "ε"
      ) @ "<> Nat",
      effects = TDef(qn = qn"archon.builtin.effects.total")
    ) @ "Nat -> <> Nat",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ "Nat -> Nat -> <> Nat",
  clauses = List(
    TClause(
      patterns = List(
        TcPattern(pattern = TpXConstructor(forced = false, name = "Zero", args = List())),
        TcPattern(pattern = TpVar(name = "n"))
      ),
      body = Some(value = TId(id = "n") @ "n")
    ),
    TClause(
      patterns = List(
        TcPattern(
          pattern = TpXConstructor(forced = false, name = "Succ", args = List(TpVar(name = "m")))
        ),
        TcPattern(pattern = TpVar(name = "n"))
      ),
      body = Some(
        value = TApp(
          f = TId(id = "Succ") @ "Succ",
          arg = TApp(
            f = TApp(f = TId(id = "plus") @ "plus", arg = TId(id = "m") @ "m") @ "plus m",
            arg = TId(id = "n")
          ) @ "plus m n"
        ) @ "Succ (plus m n"
      )
    )
  )
)