List(
  TCorecord(
    selfName = "self",
    name = "CStream",
    tParamTys = List(),
    ty = TRedex(c = TId(id = "CType") @ "CType", elims = List(ETerm(v = TId(id = "l") @ "l"))) @ "CType l",
    cofields = List(
      TCofield(name = "head", ty = TId(id = "Nat") @ "Nat"),
      TCofield(
        name = "tail",
        ty = TFunctionType(
          arg = TBinding(
            name = "m",
            ty = TId(id = "Nat"),
            usage = TDef(qn = qn"archon.builtin.type.Usage.uAny") @ "ε"
          ),
          bodyType = TFunctionType(
            arg = TBinding(
              name = "_",
              ty = TRedex(
                c = TId(id = "Eq") @ "Eq",
                elims = List(
                  ETerm(v = TId(id = "Nat")),
                  ETerm(v = TId(id = "m") @ "m"),
                  ETerm(
                    v = TRedex(
                      c = TId(id = "head") @ "head",
                      elims = List(ETerm(v = TId(id = "self") @ "self"))
                    ) @ "head self"
                  )
                )
              ) @ "Eq Nat m (head self)",
              usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
            ),
            bodyType = TId(id = "CStream") @ "CStream",
            effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε",
            escapeStatus = EsUnknown
          ) @ "Eq Nat m (head self) -> CStream",
          effects = TDef(qn = qn"archon.builtin.effects.total"),
          escapeStatus = EsUnknown
        ) @ "m: Nat -> Eq Nat m (head self) -> CStream"
      )
    )
  )
)