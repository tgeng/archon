package com.github.tgeng.archon.core.common

enum Name extends Comparable[Name]:
  case Normal(value: String)
  case Generated(value: String)
  case Unreferenced

  override def compareTo(that: Name): Int = (this, that) match
    case _ if this == that => 0
    case (Generated(thisValue), Generated(thatValue)) =>
      thisValue.compareTo(thatValue)
    case (Normal(thisValue), Normal(thatValue)) =>
      thisValue.compareTo(thatValue)
    case _ => this.ordinal.compareTo(that.ordinal)

  override def toString: String = this match
    case Normal(v)    => v
    case Generated(v) => "$" + v
    case Unreferenced => "_"

  def deriveNameWithoutConflicts(namesToAvoid: Set[Name]): Name = this match
    case Unreferenced => throw IllegalArgumentException()
    case Normal(n) =>
      val prefixEnd = n.lastIndexWhere(c => !c.isDigit) + 1
      val prefix = n.substring(0, prefixEnd).nn
      var suffix = n.substring(prefixEnd, n.length).nn.toIntOption.getOrElse(1)
      var name = n
      while namesToAvoid(Normal(name)) do
        name = prefix + suffix
        suffix += 1
      Normal(name)
    case Generated(n) =>
      val prefixEnd = n.lastIndexWhere(c => !c.isDigit) + 1
      val prefix = n.substring(0, prefixEnd).nn
      var suffix = n.substring(prefixEnd, n.length).nn.toIntOption.getOrElse(1)
      var name = prefix
      while namesToAvoid(Generated(name)) do
        name = prefix + suffix
        suffix += 1
      Generated(name)

import com.github.tgeng.archon.core.common.Name.*

enum QualifiedName extends Comparable[QualifiedName]:
  case Root
  case Node(override val parent: QualifiedName, name: Name)

  override def compareTo(that: QualifiedName): Int = (this, that) match
    case _ if this == that => 0
    case (Root, _)         => -1
    case (_, Root)         => 1
    case (Node(thisParent, thisName), Node(thatParent, thatName)) =>
      thisParent.compareTo(thatParent) match
        case 0 => thisName.compareTo(thatName)
        case r => r

  override def toString: String = this match
    case Root               => "<root>"
    case Node(Root, name)   => s"$name"
    case Node(parent, name) => s"$parent.$name"

  infix def /(name: Name): QualifiedName = Node(this, name)

  infix def /(s: String): QualifiedName = Node(this, Normal(s))

  infix def /#(s: String): QualifiedName = Node(this, Generated(s))

  def shortName: Name = this match
    case Root          => throw IllegalArgumentException()
    case Node(_, name) => name

  def parent: QualifiedName = throw IllegalArgumentException()

import com.github.tgeng.archon.core.common.QualifiedName.*

object QualifiedName:
  def from(string: String): QualifiedName =
    string.split('.').foldLeft(Root) { (p, n) =>
      if n.startsWith("#") then p /# n.drop(1) else p / n
    }

  def from(names: Seq[Name]): QualifiedName = names.foldLeft(Root)(_ / _)

  def Builtin: QualifiedName = Root / "archon" / "builtin"

extension (ctx: StringContext)
  def qn(args: Any*) = QualifiedName.from(ctx.s(args*))
  def n(args: Any*) = Name.Normal(ctx.s(args*))
  def gn(args: Any*) = Name.Generated(ctx.s(args*))
