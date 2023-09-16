package com.github.tgeng.archon.core.ir

/** A type is eqDecidable if the equality of its inhabitants can be efficiently determined at runtime. That is, a type
  * is not eqDecidable if its inhabitants
  *   - contain thunks because in general there is no way to decide equality of computations
  *   - contain erased parts whose equality can not be derived from non-erased parts and hence there is no way to decide
  *     equality at runtime
  *
  * The primary purpose of this type is to limit what types are allowed as args to effects. Efficient methods of
  * deciding equality is needed for runtime handler resolution.
  *
  * In future, it's also likely that we can introduce some built-in hashing data structure that can leverage this as a
  * bound for the key type.
  */
enum EqDecidability:
  case EqDecidable, EqUnknown

  infix def |(that: EqDecidability): EqDecidability = (this, that) match
    case (EqDecidable, _) | (_, EqDecidable) => EqDecidable
    case _                                   => EqUnknown
