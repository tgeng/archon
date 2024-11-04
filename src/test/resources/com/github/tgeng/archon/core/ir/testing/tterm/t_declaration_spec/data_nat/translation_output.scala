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
  )
)