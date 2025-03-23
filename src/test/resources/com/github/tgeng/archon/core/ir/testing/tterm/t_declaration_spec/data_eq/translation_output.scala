List(
  PreData(
    qn = qn"test.Eq",
    tParamTys = List(
      (
        Binding(
          ty = Def(qn = qn"__unresolved__.Level") @ "Level",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
        ) @ "l",
        INVARIANT
      ),
      (
        Binding(
          ty = Redex(
            t = Def(qn = qn"__unresolved__.Type") @ "Type",
            elims = List(ETerm(v = Var(idx = 0) @ "l"))
          ) @ "Type l",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny")
        ) @ "A",
        INVARIANT
      ),
      (
        Binding(
          ty = Return(v = Var(idx = 0) @ "A", usage = Auto() @ "ε") @ "A",
          usage = Def(qn = qn"archon.builtin.type.Usage.uAny")
        ) @ "x",
        INVARIANT
      )
    ),
    ty = FunctionType(
      binding = Binding(
        ty = Var(idx = 1) @ "A",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny")) @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(
          cTm = Redex(
            t = Def(qn = qn"__unresolved__.Type") @ "Type",
            elims = List(ETerm(v = Var(idx = 3) @ "l"))
          ) @ "Type l"
        ) @ "Type l",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1") @ "ε") @ "ε"
      ) @ "Type l",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
      escapeStatus = EsUnknown
    ) @ "A -> Type l",
    constructors = List(
      PreConstructor(
        name = n"Refl",
        ty = F(
          vTy = DataType(
            qn = qn"test.Eq",
            args = List(
              Var(idx = 2) @ "l",
              Var(idx = 1) @ "A",
              Var(idx = 0) @ "x",
              Var(idx = 0) @ "x"
            )
          ) @ "Eq l A x x",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1"))
        ) @ "Eq l A x x"
      )
    ),
    interfaceScope = qn"<root>",
    implementationScope = qn"<root>"
  )
)