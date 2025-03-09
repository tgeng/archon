/** Visibilities are set on two things: head and body, where head should always have an equal or
  * less restrictive visibility.
  *
  * For both head and body, visibility setting controls at which scope the entity is visible, where
  * scope is basically the fully qualified name of the current declaration that's being elaborated
  * currently.
  *
  * For example, a definition called `baz` in module `foo.bar` has fully qualified name
  * `foo.bar.baz`. If a declaration is declared to be visible to scope `foo.bar`, then that
  * declaration can be accessed when * elaborating `foo.bar.baz`.
  *
  * This mechanism can be used to model common visibility idioms seen in various programming
  * languages.
  *
  *   - public export in idris: this means a declaration is public for both its head and body (aka
  *     signature and implementation). That is,
  *     - head: _root_
  *     - body: _root_
  *   - public in idris: this means a declaration's head is public but body is module accessible
  *     - head: _root_
  *     - body: %parent% (aka, `foo.bar` for `foo.bar.baz`)
  *   - opaque type: this means the head is public, yet the body is private to itself (of course one
  *     can limit the "opaqueness" by setting the appropriate body visibility scope. Note: the type
  *     is not opaque for member declarations in its scope, this way, one can still create helper
  *     functions to manipulate this opaque type
  *     - head: _root_
  *     - body: %current% (aka `foo.bar.baz` for `foo.bar.baz`)
  *   - common private in most languages:
  *     - head: %parent%
  *     - body: %current%
  *
  * In addition, visibility consistency needs to be checked. That is, during elaboration of a head
  * or a body, the type checker must ensure all the declarations accessed align with the declared
  * visibility scope of the thing being elaborated. For example, when elaborating head of
  * `foo.bar.baz`, which has visibility scope `_root_`, in addition to ensure the referenced thing
  * is visible to scope `foo.bar.baz`, the type checker also needs to ensure it is visible to
  * `_root_`. Otherwise, `foo.bar.baz` would be exposing things that are not visible to `_root_`.
  */

object visibility
