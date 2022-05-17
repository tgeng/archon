package com.github.tgeng.archon.core.ast

import com.github.tgeng.archon.common.*
import com.github.tgeng.archon.core.common.*
import com.github.tgeng.archon.core.ir.*

type AstTTelescope = List[(Name, AstTerm, Variance)]
type AstTelescope = List[(Name, AstTerm)]

enum AstSignature:
  case AstData(qn: QualifiedName, tParamTys: List[(Name, AstTerm, Variance)], ty: AstTerm, isPure: Boolean)
  case AstRecord(qn: QualifiedName, tParamTys: List[(Name, AstTerm, Variance)], ty: AstTerm)
  case AstDefinition(qn: QualifiedName, ty: AstTerm)
  case AstEffect(qn: QualifiedName, tParamTys: AstTelescope)
