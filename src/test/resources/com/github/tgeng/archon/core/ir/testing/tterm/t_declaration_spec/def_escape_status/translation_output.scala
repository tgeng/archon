List(
  PreDefinition(
    qn = qn"test.foo",
    paramTys = List(
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Nat") @ "Nat",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
        ) @ "x",
        EsLocal
      ),
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Nat") @ "Nat",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny")
        ) @ "y",
        EsReturned
      ),
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Nat") @ "Nat",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny")
        ) @ "z",
        EsUnknown
      )
    ),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny")) @ "ε"
      ) @ "_",
      bodyTy = FunctionType(
        binding = Binding(
          ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
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
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          escapeStatus = EsUnknown
        ) @ "Nat -> <> Nat",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
        escapeStatus = EsReturned
      ) @ "Nat -> esc Nat -> <> Nat",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
      escapeStatus = EsLocal
    ) @ "Nat -> ret Nat -> esc Nat -> <> Nat",
    clauses = List(
      PreClause(
        boundNames = List("a", "b", "c"),
        lhs = List(
          CPattern(pattern = PVar(idx = 2)),
          CPattern(pattern = PVar(idx = 1)),
          CPattern(pattern = PVar(idx = 0))
        ),
        rhs = Some(value = Return(v = Var(idx = 1) @ "b", usage = Auto()) @ "b")
      )
    ),
    interfaceScope = qn"<root>",
    implementationScope = qn"<root>"
  )
)