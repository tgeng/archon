TDefinition(
  name = "plus",
  tParamTys = List(),
  ty = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TId(id = "Nat") @ "Nat",
      usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
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
        value = TRedex(
          c = TId(id = "Succ") @ "Succ",
          elims = List(
            ETerm(
              v = TRedex(
                c = TId(id = "plus") @ "plus",
                elims = List(ETerm(v = TId(id = "m") @ "m"), ETerm(v = TId(id = "n")))
              ) @ "plus m n"
            )
          )
        ) @ "Succ (plus m n)"
      )
    )
  )
)