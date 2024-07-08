List(
  TData(
    name = "Vec",
    tParamTys = List(
      (
        TBinding(
          name = "l",
          ty = TId(id = "Level") @ "Level",
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
        ),
        INVARIANT
      ),
      (
        TBinding(
          name = "t",
          ty = TRedex(c = TId(id = "Type") @ "Type", elims = List(ETerm(v = TId(id = "l") @ "l"))) @ "Type l",
          usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
        ),
        COVARIANT
      )
    ),
    ty = TFunctionType(
      arg = TBinding(
        name = "_",
        ty = TId(id = "Nat") @ "Nat",
        usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
      ),
      bodyType = TF(
        ty = TRedex(c = TId(id = "Type"), elims = List(ETerm(v = TId(id = "l")))),
        effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
        usage = TDef(qn = qn"archon.builtin.type.Usage.u1") @ "ε"
      ) @ "Type l",
      effects = TDef(qn = qn"archon.builtin.effects.total")
    ) @ "Nat -> Type l",
    constructors = List(
      TConstructor(
        name = "Nil",
        ty = TF(
          ty = TRedex(
            c = TId(id = "Vec") @ "Vec",
            elims = List(
              ETerm(v = TId(id = "l")),
              ETerm(v = TId(id = "t") @ "t"),
              ETerm(v = TId(id = "Zero") @ "Zero")
            )
          ) @ "Vec l t Zero",
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          usage = TDef(qn = qn"archon.builtin.type.Usage.u1")
        ) @ "Vec l t Zero"
      ),
      TConstructor(
        name = "Succ",
        ty = TFunctionType(
          arg = TBinding(
            name = "n",
            ty = TId(id = "Nat"),
            usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
          ),
          bodyType = TFunctionType(
            arg = TBinding(
              name = "_",
              ty = TId(id = "t"),
              usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
            ),
            bodyType = TFunctionType(
              arg = TBinding(
                name = "_",
                ty = TRedex(
                  c = TId(id = "Vec"),
                  elims = List(
                    ETerm(v = TId(id = "l")),
                    ETerm(v = TId(id = "t")),
                    ETerm(v = TId(id = "n") @ "n")
                  )
                ) @ "Vec l t n",
                usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
              ),
              bodyType = TF(
                ty = TRedex(
                  c = TId(id = "Vec"),
                  elims = List(
                    ETerm(v = TId(id = "l")),
                    ETerm(v = TId(id = "t")),
                    ETerm(
                      v = TRedex(
                        c = TId(id = "Succ") @ "Succ",
                        elims = List(ETerm(v = TId(id = "n")))
                      ) @ "Succ n"
                    )
                  )
                ) @ "Vec l t (Succ n)",
                effects = TDef(qn = qn"archon.builtin.effects.total"),
                usage = TDef(qn = qn"archon.builtin.type.Usage.u1")
              ) @ "Vec l t (Succ n)",
              effects = TDef(qn = qn"archon.builtin.effects.total")
            ) @ "Vec l t n -> Vec l t (Succ n)",
            effects = TDef(qn = qn"archon.builtin.effects.total")
          ) @ "t -> Vec l t n -> Vec l t (Succ n)",
          effects = TDef(qn = qn"archon.builtin.effects.total")
        ) @ "n: Nat -> t -> Vec l t n -> Vec l t (Succ n)"
      )
    )
  )
)