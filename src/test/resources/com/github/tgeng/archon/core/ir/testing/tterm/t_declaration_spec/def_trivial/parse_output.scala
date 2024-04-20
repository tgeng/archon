TDefinition(
  name = "foo",
  tParamTys = List(),
  ty = TFunctionType(
    arg = TBinding(
      name = "_",
      ty = TId(id = "Nat") @ "Nat",
      usage = TDef(qn = qn"archon.builtin.type.Usage.any") @ "ε"
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
      patterns = List(TcPattern(pattern = TpVar(name = "n"))),
      body = Some(
        value = TApp(
          f = TApp(f = TId(id = "plus") @ "plus", arg = TId(id = "n") @ "n") @ "plus n",
          arg = TApp(f = TId(id = "Suc") @ "Suc", arg = TId(id = "Zero") @ "Zero") @ "Suc Zero"
        ) @ "plus n (Suc Zero"
      )
    )
  )
)