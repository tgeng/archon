List(
  PreData(
    qn = qn"test.Nat",
    tParamTys = List(),
    ty = Let(
      t = F(
        vTy = Collapse(
          cTm = Let(
            t = Redex(
              t = Def(qn = qn"__unresolved__.Type") @ "Type",
              elims = List(
                ETerm(v = Level(literal = LevelOrder(m = 0, n = 0), maxOperands = SeqMap()) @ "0L")
              )
            ) @ "Type 0L",
            ty = Auto() @ "ε",
            eff = Auto(),
            usage = Auto(),
            body = Return(v = Var(idx = 0) @ "ε", usage = Auto()) @ "ε"
          ) @ "ε"
        ) @ "ε",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one") @ "ε") @ "ε"
      ) @ "Type 0L",
      ty = Auto(),
      eff = Auto(),
      usage = Auto(),
      body = Return(v = Var(idx = 0), usage = Auto())
    ) @ "ε",
    constructors = List(
      PreConstructor(
        name = n"Zero",
        ty = Let(
          t = F(
            vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "ε",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
          ) @ "Nat",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      ),
      PreConstructor(
        name = n"Succ",
        ty = Let(
          t = FunctionType(
            binding = Binding(
              ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.any") @ "ε") @ "ε"
            ) @ "_",
            bodyTy = Let(
              t = F(
                vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat"),
                effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
                usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.one"))
              ) @ "Nat",
              ty = Auto(),
              eff = Auto(),
              usage = Auto(),
              body = Return(v = Var(idx = 0), usage = Auto())
            ),
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
          ) @ "Nat -> Nat",
          ty = Auto(),
          eff = Auto(),
          usage = Auto(),
          body = Return(v = Var(idx = 0), usage = Auto())
        ) @ "ε"
      )
    )
  )
)