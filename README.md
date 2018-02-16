## Beyond Good and Evil: Formalizing the Security Guarantees of Compartmentalizing Compilation

This repository contains auxiliary materials for the following paper:

- Yannis Juglaret, Cătălin Hriţcu, Arthur Azevedo de Amorim, Boris Eng, and Benjamin C. Pierce.
  Beyond Good and Evil: Formalizing the Security Guarantees of Compartmentalizing Compilation.
  In 29th IEEE Symposium on Computer Security Foundations (CSF), pages 45–60.
  IEEE Computer Society Press, July 2016. Technical report https://arxiv.org/abs/1602.04503

In particular, these materials include:
- `sfa-to-scc-coq`: a Coq proof for Theorem 3.4 showing that Structured Full Abstraction
  instantiated to components implies Secure Compartmentalizing Compilation (SCC)
- `simple-instance.org`and `simple-instance-coq`: technical details
  and proofs showing that the simple compiler from Section 4 satisfies SCC
  (both on paper and in Coq)
- `trace-mapping-testing`: a trace mapping algorithm in OCaml using property-based testing
  to check the Definability assumption from Section 4

The code in this repository is licensed under the Apache License, Version 2.0 (see `LICENSE`)
