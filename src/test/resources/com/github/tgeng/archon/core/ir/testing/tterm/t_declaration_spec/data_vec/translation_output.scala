List(
  PreData(
    qn = qn"test.Vec",
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
        ) @ "t",
        COVARIANT
      )
    ),
    ty = FunctionType(
      binding = Binding(
        ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny")) @ "ε"
      ) @ "_",
      bodyTy = F(
        vTy = Collapse(
          cTm = Redex(
            t = Def(qn = qn"__unresolved__.Type") @ "Type",
            elims = List(ETerm(v = Var(idx = 2) @ "l"))
          ) @ "Type l"
        ) @ "Type l",
        effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total") @ "ε") @ "ε",
        usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1") @ "ε") @ "ε"
      ) @ "Type l",
      effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
    ) @ "Nat -> Type l",
    constructors = List(
      PreConstructor(
        name = n"Nil",
        ty = F(
          vTy = DataType(
            qn = qn"test.Vec",
            args = List(
              Var(idx = 1) @ "l",
              Var(idx = 0) @ "t",
              Collapse(cTm = Def(qn = qn"__unresolved__.Zero") @ "Zero") @ "Zero"
            )
          ) @ "Vec l t Zero",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
          usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1"))
        ) @ "Vec l t Zero"
      ),
      PreConstructor(
        name = n"Succ",
        ty = FunctionType(
          binding = Binding(
            ty = Collapse(cTm = Def(qn = qn"__unresolved__.Nat") @ "Nat") @ "Nat",
            usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
          ) @ "n",
          bodyTy = FunctionType(
            binding = Binding(
              ty = Var(idx = 1) @ "t",
              usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
            ) @ "_",
            bodyTy = FunctionType(
              binding = Binding(
                ty = DataType(
                  qn = qn"test.Vec",
                  args = List(Var(idx = 3) @ "l", Var(idx = 2) @ "t", Var(idx = 1) @ "n")
                ) @ "Vec l t n",
                usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.uAny"))
              ) @ "_",
              bodyTy = F(
                vTy = DataType(
                  qn = qn"test.Vec",
                  args = List(
                    Var(idx = 4) @ "l",
                    Var(idx = 3) @ "t",
                    Con(name = n"Succ", args = List(Var(idx = 2) @ "n")) @ "Succ n"
                  )
                ) @ "Vec l t (Succ n)",
                effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total")),
                usage = Collapse(cTm = Def(qn = qn"archon.builtin.type.Usage.u1"))
              ) @ "Vec l t (Succ n)",
              effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
            ) @ "Vec l t n -> Vec l t (Succ n)",
            effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
          ) @ "t -> Vec l t n -> Vec l t (Succ n)",
          effects = Collapse(cTm = Def(qn = qn"archon.builtin.effects.total"))
        ) @ "n: Nat -> t -> Vec l t n -> Vec l t (Succ n)"
      )
    )
  )
)