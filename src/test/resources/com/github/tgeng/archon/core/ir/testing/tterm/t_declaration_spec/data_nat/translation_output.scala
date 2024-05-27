List(
  PreData(
    qn = qn"test.Nat",
    tParamTys = List(),
    ty = F(
      vTy = Collapse(
        cTm = Redex(
          t = Def(qn = qn"__unresolved__.Type") @ "Type",
          elims = List(
            ETerm(
              v = Collapse(
                cTm = Return(
                  v = Level(literal = LevelOrder(m = 0, n = 0), maxOperands = SeqMap()) @ "0L",
                  usage = Auto() @ "ε"
                ) @ "0L"
              ) @ "ε"
            )
          )
        ) @ "Type 0L"
      ) @ "ε",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
      usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε") @ "ε"
    ) @ "Type 0L",
    constructors = List(
      PreConstructor(
        name = n"Zero",
        ty = F(
          vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
        ) @ "Nat"
      ),
      PreConstructor(
        name = n"Succ",
        ty = FunctionType(
          binding = Binding(
            ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
          ) @ "_",
          bodyTy = F(
            vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
          ) @ "Nat",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
        ) @ "Nat -> Nat"
      )
    )
  )
)