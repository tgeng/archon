package io.github.tgeng.archon.ir

import VTerm.*
import CTerm.*

trait ConstraintSystem:
  def addEquality(a: VTerm, b: VTerm): Either[Error, Unit]
  def addLevelLe(a: VTerm, b: VTerm): Either[Error, Unit]
  def addEffectLe(a: VTerm, b: VTerm): Either[Error, Unit]
  

def checkVType(tm: VTerm, ty: VTerm)(using Γ: Context)(using Σ: Signature)(using sys: ConstraintSystem): Either[Error, Unit] =
  tm match
    case VUniverse(l1) => ty match
      case VUniverse(l2) => sys.addEquality(l1 /* + 1 */, l2)

def inferVLevel(tm: VTerm)(using Γ: Context)(using Σ: Signature): Either[Error, VTerm] = ???

def inferCType(tm: CTerm)(using Γ: Context)(using Σ: Signature): Either[Error, CTerm] = ???