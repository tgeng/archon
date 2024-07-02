TDefinition(
  name = "foo",
  tParamTys = List(),
  ty = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TId(id = "Nat") @ "Nat",
      usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
    ),
    bodyType = TF(
      ty = TId(id = "Nat"),
      effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
      usage = TAuto() @ "ε"
    ) @ "<> Nat",
    effects = TDef(qn = qn"archon.builtin.effects.total")
  ) @ "Nat -> <> Nat",
  clauses = List(
    TClause(
      patterns = List(TcPattern(pattern = TpId(name = "n"))),
      body = Some(
        value = TRedex(
          c = TId(id = "plus") @ "plus",
          elims = List(
            ETerm(v = TId(id = "n") @ "n"),
            ETerm(
              v = TRedex(
                c = TId(id = "Suc") @ "Suc",
                elims = List(ETerm(v = TId(id = "Zero") @ "Zero"))
              ) @ "Suc Zero"
            )
          )
        ) @ "plus n (Suc Zero)"
      )
    )
  )
)