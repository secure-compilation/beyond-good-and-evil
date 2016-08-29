
A Coq proof accompanying the "Beyond Good and Evil" paper
=========================================================

This proof shows that Structured Full Abstraction instantiated to
components implies Secure Compartmentalizing Compilation (Theorem 3.4
in the "Beyond Good and Evil" paper).

This development is known to compile with Coq v8.4 (at least version
8.4pl5) as well as with Coq v8.5pl2.

The definitions of structured full abstraction are in the file
`fullabst.v`. `context_language` and `structured_context_language`
comprise the basic language definitions needed to state the property.

The `seccomp.v` file defines the basic notions of a compartmentalized
language and the `secure_compartmentalization` property (called Secure
Compartmentalizing Compilation in the latest version of the
paper). `sfa_implies_sc` shows that, if structured full abstraction
holds for a compartmentalized language, then secure
compartmentalization also does.
