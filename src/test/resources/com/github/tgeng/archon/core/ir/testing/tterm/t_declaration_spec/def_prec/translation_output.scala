List(
  PreDefinition(
    qn = qn"test.prec",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"test.Nat") @ ".test.Nat") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(cTm = Def(qn = qn"test.Nat") @ ".test.Nat"),
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Return(v = Auto() @ "ε", usage = Auto()) @ "ε") @ "ε"
      ) @ "<> .test.Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ ".test.Nat -> <> .test.Nat",
    clauses = List(
      PreClause(
        boundNames = List(),
        lhs = List(CPattern(pattern = PDataType(qn = qn"__unresolved__.Zero", args = List()))),
        rhs = Some(value = Def(qn = qn"test.Nat.Zero") @ ".test.Nat.Zero")
      ),
      PreClause(
        boundNames = List("m"),
        lhs = List(
          CPattern(pattern = PDataType(qn = qn"__unresolved__.Succ", args = List(PVar(idx = 0))))
        ),
        rhs = Some(value = Return(v = Var(idx = 0) @ "m", usage = Auto()) @ "m")
      )
    )
  )
)