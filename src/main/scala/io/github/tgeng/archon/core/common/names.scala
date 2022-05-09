package io.github.tgeng.archon.core.common

enum Name:
  case Normal(value: String)
  case Generated(value: String)

  override def toString: String = this match
    case Normal(v) => v
    case Generated(v) => s"#$v"

import Name.*

enum QualifiedName:
  case Root
  case Node(parent: QualifiedName, name: Name)

  override def toString: String = this match
    case Root => ".root"
    case Node(parent, name) => s"$parent/$name"

  infix def /(name: Name): QualifiedName = Node(this, name)

  infix def /(s: String): QualifiedName = Node(this, Normal(s))

  infix def /#(s: String): QualifiedName = Node(this, Generated(s))

import QualifiedName.*

object QualifiedName:
  def from(string: String) = string.split('.').asInstanceOf[Array[String]].foldLeft(Root) { (p, n) =>
    if n.startsWith("#") then p /# n.drop(1) else p / n
  }
  def Builtin = Root / "archon" / "builtin"

extension (ctx: StringContext)
  def qn(args: String*) = QualifiedName.from(ctx.s(args: _*))
  def gn(args: String*) = Name.Generated(ctx.s(args: _*))
  def n(args: String*) = Name.Normal(ctx.s(args: _*))
