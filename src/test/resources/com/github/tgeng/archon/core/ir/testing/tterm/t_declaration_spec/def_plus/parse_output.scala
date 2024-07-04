List(
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
          TcPattern(pattern = TpId(name = "Zero")),
          TcPattern(pattern = TpId(name = "n"))
        ),
        body = Some(value = TId(id = "n") @ "n")
      ),
      TClause(
        patterns = List(
          TcPattern(
            pattern = TpXConstructor(forced = false, name = "Succ", args = List(TpId(name = "m")))
          ),
          TcPattern(pattern = TpId(name = "n"))
        ),
        body = Some(
          value = TCon(
            name = "Succ",
            args = List(TId(id = "plus") @ "plus", TId(id = "m") @ "m", TId(id = "n"))
          ) @ "Succ#{plus m n}"
        )
      )
    )
  )
)