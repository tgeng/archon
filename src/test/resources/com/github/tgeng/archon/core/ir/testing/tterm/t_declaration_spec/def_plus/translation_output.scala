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
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
        ) @ "Nat -> Nat"
      )
    )
  ),
  PreDefinition(
    qn = qn"test.plus",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
      ) @ "_",
      bodyTy = FunctionType(
        binding = Binding(
          ty = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
        ) @ "_",
        bodyTy = F(
          vTy = DataType(qn = qn"test.Nat", args = List()) @ "Nat",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Auto() @ "ε"
        ) @ "<> Nat",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "Nat -> <> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "Nat -> Nat -> <> Nat",
    clauses = List(
      PreClause(
        boundNames = List("n"),
        lhs = List(
          CPattern(pattern = PConstructor(name = n"Zero", args = List())),
          CPattern(pattern = PVar(idx = 0))
        ),
        rhs = Some(value = Return(v = Var(idx = 0) @ "n", usage = Auto()) @ "n")
      ),
      PreClause(
        boundNames = List("m", "n"),
        lhs = List(
          CPattern(pattern = PConstructor(name = n"Succ", args = List(PVar(idx = 1)))),
          CPattern(pattern = PVar(idx = 0))
        ),
        rhs = Some(
          value = Let(
            t = Redex(
              t = Def(qn = qn"test.plus") @ "plus",
              elims = List(ETerm(v = Var(idx = 1) @ "m"), ETerm(v = Var(idx = 0) @ "n"))
            ) @ "plus m n",
            tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
            eff = Auto(),
            body = Return(
              v = Con(name = n"Succ", args = List(Var(idx = 0) @ "plus m n")) @ "Succ (plus m n)",
              usage = Auto()
            ) @ "Succ (plus m n)"
          ) @ "ε"
        )
      )
    )
  )
)