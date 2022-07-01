package com.github.tgeng.archon.core.common

enum Name extends Comparable[Name] :
  case Normal(value: String)
  case Generated(value: String)

  override def compareTo(that: Name): Int = (this, that) match
    case _  if this == that => 0
    case (Generated(thisValue), Generated(thatValue)) => thisValue.compareTo(thatValue)
    case (Normal(thisValue), Normal(thatValue)) => thisValue.compareTo(thatValue)
    case _ => this.ordinal.compareTo(that.ordinal)

  override def toString: String = this match
    case Normal(v) => v
    case Generated(v) => s"#$v"

import Name.{Generated, *}

enum QualifiedName extends Comparable[QualifiedName] :
  case Root
  case Node(parent: QualifiedName, name: Name)

  override def compareTo(that: QualifiedName): Int = (this, that) match
    case _ if this == that => 0
    case (Root, _) => -1
    case (_, Root) => 1
    case (Node(thisParent, thisName), Node(thatParent, thatName)) =>
      thisParent.compareTo(thatParent) match
        case 0 => thisName.compareTo(thatName)
        case r => r

  override def toString: String = this match
    case Root => "<root>"
    case Node(Root, name) => s"$name"
    case Node(parent, name) => s"$parent.$name"

  infix def /(name: Name): QualifiedName = Node(this, name)

  infix def /(s: String): QualifiedName = Node(this, Normal(s))

  infix def /#(s: String): QualifiedName = Node(this, Generated(s))

import QualifiedName.*

object QualifiedName:
  def from(string: String) = string.split('.').asInstanceOf[Array[String]].foldLeft(Root) { (p, n) =>
    if n.startsWith("#") then p /# n.drop(1) else p / n
  }

  def from(names: Seq[Name]) = names.foldLeft(Root)(_ / _)

  def Builtin = Root / "archon" / "builtin"

extension (ctx: StringContext)
  def qn(args: String*) = QualifiedName.from(ctx.s(args: _*))
  def gn(args: String*) = Name.Generated(ctx.s(args: _*))
  def n(args: String*) = Name.Normal(ctx.s(args: _*))
