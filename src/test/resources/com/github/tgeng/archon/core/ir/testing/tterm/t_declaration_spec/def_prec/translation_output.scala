List(
  PreData(
    qn = qn"test.Nat",
    tParamTys = List(),
    ty = F(
      vTy = Collapse(
        cTm = Redex(
          t = Def(qn = qn"__unresolved__.Type") @ "Type",
          elims = List(
            ETerm(v = Level(literal = LevelOrder(m = 0, n = 0), maxOperands = SeqMap()) @ "0L")
          )
        ) @ "Type 0L"
      ) @ "Type 0L",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1") @ "ε") @ "ε"
    ) @ "Type 0L",
    constructors = List(
      PreConstructor(
        name = n"Zero",
        ty = F(
          vTy = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1"))
        ) @ "Nat"
      ),
      PreConstructor(
        name = n"Succ",
        ty = FunctionType(
          binding = Binding(
            ty = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
          ) @ "_",
          bodyTy = F(
            vTy = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1"))
          ) @ "Nat",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          escapeStatus = EsUnknown
        ) @ "Nat -> Nat"
      )
    )
  ),
  PreDefinition(
    qn = qn"test.prec",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
      ) @ "_",
      bodyTy = F(
        vTy = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
        usage = Auto() @ "ε"
      ) @ "<> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
      escapeStatus = EsUnknown
    ) @ "Nat -> <> Nat",
    clauses = List(
      PreClause(
        boundNames = List(),
        lhs = List(CPattern(pattern = PConstructor(name = n"Zero", args = List()))),
        rhs = Some(
          value = Return(v = Con(name = n"Zero", args = List()) @ "Zero", usage = Auto()) @ "Zero"
        )
      ),
      PreClause(
        boundNames = List("m"),
        lhs = List(CPattern(pattern = PConstructor(name = n"Succ", args = List(PVar(idx = 0))))),
        rhs = Some(value = Return(v = Var(idx = 0) @ "m", usage = Auto()) @ "m")
      )
    )
  )
)