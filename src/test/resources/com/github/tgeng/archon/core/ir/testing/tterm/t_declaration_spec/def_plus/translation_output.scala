List(
  PreDefinition(
    qn = qn"test.plus",
    paramTys = List(),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε") @ "ε"
      ) @ "_",
      bodyTy = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
        ) @ "_",
        bodyTy = F(
          vTy = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
          usage = Auto() @ "ε"
        ) @ "<> Nat",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
      ) @ "Nat -> <> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "Nat -> Nat -> <> Nat",
    clauses = List(
      PreClause(
        boundNames = List("Zero", "n"),
        lhs = List(CPattern(pattern = PVar(idx = 1)), CPattern(pattern = PVar(idx = 0))),
        rhs = Some(value = Return(v = Var(idx = 0) @ "n", usage = Auto()) @ "n")
      ),
      PreClause(
        boundNames = List("m", "n"),
        lhs = List(
          CPattern(pattern = PDataType(qn = qn"__unresolved__.Succ", args = List(PVar(idx = 1)))),
          CPattern(pattern = PVar(idx = 0))
        ),
        rhs = Some(
          value = Let(
            t = Def(qn = qn"test.plus") @ "plus",
            tBinding = Binding(ty = Auto(), usage = Auto()) @ "$v",
            eff = Auto(),
            body = Return(
              v = Con(
                name = n"Succ",
                args = List(Var(idx = 0) @ "plus", Var(idx = 1) @ "m", Var(idx = 0) @ "n")
              ) @ "Succ#{plus m n}",
              usage = Auto()
            ) @ "Succ#{plus m n}"
          ) @ "ε"
        )
      )
    )
  )
)