# Otter

Otter is an experimental programming language that combines Go's syntax, Rust's ownership model, and Z3's automated theorem proving.

It solves the biggest hurdle in formal methods—the Frame Problem—by enforcing strict memory ownership at the language level. If the code compiles, the SMT solver knows exactly what memory didn't change, without you writing a single line of modifies annotations.

## Why Otter?

In traditional verification tools (like Dafny or Frama-C), proving that a function update(a) didn't corrupt b requires complex logical annotations (Separation Logic or Dynamic Frames).

Otter flips the script:

1. Ownership First: The compiler's Borrow Checker guarantees that two mutable references never alias.

2. Pure Logic: Because aliasing is impossible, the compiler transforms imperative code into strict Static Single Assignment (SSA) form.

3. Fast Verification: The SMT solver (Z3) receives clean, functional constraints. No heap modeling required.
