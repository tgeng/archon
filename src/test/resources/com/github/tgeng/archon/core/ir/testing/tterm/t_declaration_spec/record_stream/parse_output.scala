TRecord(
  selfName = "self",
  name = "CStream",
  tParamTys = List(),
  ty = TApp(f = TId(id = "CType") @ "CType", arg = TId(id = "l") @ "l") @ "CType l",
  fields = List(
    TField(name = "head", ty = TId(id = "Nat") @ "Nat"),
    TField(
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
            ty = TApp(
              f = TApp(
                f = TApp(f = TId(id = "Eq") @ "Eq", arg = TId(id = "Nat")) @ "Eq Nat",
                arg = TId(id = "m") @ "m"
              ) @ "Eq Nat m",
              arg = TApp(f = TId(id = "head") @ "head", arg = TId(id = "self") @ "self") @ "head self"
            ) @ "Eq Nat m (head self",
            usage = TDef(qn = qn"archon.builtin.type.Usage.uAny")
          ),
          bodyType = TId(id = "CStream") @ "CStream",
          effects = TDef(qn = qn"archon.builtin.effects.total") @ "ε"
        ) @ "Eq Nat m (head self) -> CStream",
        effects = TDef(qn = qn"archon.builtin.effects.total")
      ) @ "m: Nat -> Eq Nat m (head self) -> CStream"
    )
  )
)