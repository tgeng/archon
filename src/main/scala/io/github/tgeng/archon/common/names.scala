package io.github.tgeng.archon.common

enum Name:
  case Normal(value: String)
  case Generated(value: String)

  override def toString: String = this match
    case Normal(v) => v
    case Generated(v) => s"<$v>"

import io.github.tgeng.archon.common.Name.{Generated, *}

enum QualifiedName:
  case Root
  case Node(parent: QualifiedName, name: Name)

  override def toString: String = this match
    case Root => "__root"
    case Node(parent, name) => s"$parent.$name"

  infix def /(name: Name): QualifiedName = Node(this, name)

  infix def /(s: String): QualifiedName = Node(this, Normal(s))

  infix def /#(s: String): QualifiedName = Node(this, Generated(s))

import io.github.tgeng.archon.common.QualifiedName.*

object QualifiedName:
  def from(string: String) = string.split('.').asInstanceOf[Array[String]].foldLeft(Root) { (p, n) =>
    if n.startsWith("#") then p /# n.drop(1) else p / n
  }
  def Builtin = Root / "archon" / "builtin"

extension (ctx: StringContext)
  def qn(args: String*) = QualifiedName.from(ctx.s(args))
  def gn(args: String*) = Name.Generated(ctx.s(args))
  def n(args: String*) = Name.Normal(ctx.s(args))
